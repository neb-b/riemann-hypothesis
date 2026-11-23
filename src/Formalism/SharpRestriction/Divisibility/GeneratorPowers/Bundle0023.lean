module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IsUnitCoeffZero
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffAddFirstSecond
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0008
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetPointZeroEqOne
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0002
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFixAsm
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.TB (dLin)

def FrRatioSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (m : ℕ),
    ∃ U : (Jet S (Fin 2 × Fin C.d) m)ˣ,
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (C.e (m + 1))
          (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)).left)
        (scaleGen (Xo := Xo) _ _ (unitΓ U) (C.e m)) ∧
      jetSubstP m (fun p : Fin 2 × Fin C.d =>
          (![fun j => psIn C.d m (![0, 1] : Fin 2 → Fin 3) (C.B.G.F j), fun j => X ((2 : Fin 3), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) =
        jetSubstP m (fun p : Fin 2 × Fin C.d => (![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) *
        jetSubstP m (fun p : Fin 2 × Fin C.d => (![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) ∧
      jetSubstP m (fun p : Fin 2 × Fin C.d => (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) = U ∧
      ∀ a : 𝓞 E, jetSubstP m (fun p : Fin 2 × Fin C.d =>
          (![fun j => psIn C.d m ![0] (C.B.A.act a j), fun j => X ((1 : Fin 2), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) =
        jetSubstP m (fun p : Fin 2 × Fin C.d =>
          (![fun j => X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a) j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m)

def ccOf {S : Type} [CommRing S] {d : ℕ} (cm : ℕ → Fin d → Fin d → S) : ℕ → Fin d → Fin d → S
  | 0 => 0
  | m + 1 => ccOf cm m - cm m

theorem frTruncFix_of (hA : FrRatioSt) : FrTruncFixSt := by
  intro E _ _ _ H Dw l Xo c _ hstar S _ _ _ y C
  choose U hCorr h1 hs hb using fun m => hA E H Dw l Xo c hstar S y C m
  have hact : ∀ (a : 𝓞 E) (i : Fin C.d), MvPowerSeries.constantCoeff (C.B.A.act a i) = 0 :=
    fun a i => C.B.A.const a i
  choose cm hcs hcb hcU using fun m =>
    CIndFrExp3.fixExp (G := C.B.G) (act := C.B.A.act) (hact := hact) (bar := H.bar) (m := m)
      (U := U m) (h1 := h1 m) (hs := hs m) (hb := hb m)
  have hsym : ∀ m i j, ccOf cm m i j = ccOf cm m j i := by
    intro m
    induction m with
    | zero => intro i j; rfl
    | succ m ih =>
      intro i j
      show ccOf cm m i j - cm m i j = ccOf cm m j i - cm m j i
      rw [ih i j, hcs m i j]
  have hbal : ∀ m (a : 𝓞 E), Matrix.transpose (dLin (C.B.A.act a)) * Matrix.of (ccOf cm m) =
      Matrix.of (ccOf cm m) * dLin (C.B.A.act (H.bar a)) := by
    intro m
    induction m with
    | zero => intro a; simp only [ccOf, Matrix.of_zero, mul_zero, zero_mul]
    | succ m ih =>
      intro a
      simp only [ccOf]
      rw [← Matrix.of_sub_of, mul_sub, sub_mul, ih a, hcb m a]
  have hdiff : ∀ m, ccOf cm m - ccOf cm (m + 1) = cm m := fun m =>
    show ccOf cm m - (ccOf cm m - cm m) = cm m from sub_sub_cancel _ _
  obtain ⟨e', hfr, hrig, htr, hu⟩ := CIndFrFix2c.fixTw (C := C) (cc := ccOf cm) (h0 := rfl)
    (hsym := hsym) (hbal := hbal)
    (hstep := fun m => ⟨U m, by rw [hdiff m]; exact hcU m, hCorr m⟩)
  exact ⟨e', hfr, hrig, ccOf cm, htr, rfl, hsym, hbal, hu⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ESecToUnit
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem val_rigPow {Z : Scheme.{0}} (k : ℤ) (r : Z ⟶ (𝟙_ (Over Xo.X)).left) (z : Z)
    (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) :
    val (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig k) r z J = val Xo.univ.t.PP.rig r z J ^ k := by
  unfold rigPow val
  exact map_zpow _ _ _

theorem eSec_act (c : 𝓞 E) : eSec Xo.univ.t.G ≫ (Xo.univ.t.act.act c).left = eSec Xo.univ.t.G := by
  haveI := Xo.univ.t.act.2 c
  unfold eSec
  rw [← Over.comp_left, IsMonHom.one_hom]

theorem eSec_toUnit : eSec Xo.univ.t.G ≫ (toUnit Xo.univ.t.G).left = 𝟙 _ := by
  unfold eSec
  rw [← Over.comp_left]
  simp

theorem exists_beta (wP : PrimTy H Xo) (hwP : IsPrim wP) (a : 𝓞 E) (hbb : H.bar (H.bar a) = a)
    (wLa : ExpGC.AdTy Xo a) (hwa : wLa.IsGen) (wLb : ExpGC.AdTy Xo (H.bar a)) (hwb : wLb.IsGen) :
    ∃ β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε), β.IsGen ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (eSec Xo.univ.t.G))
        (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
        Good Xo.univ.t.PP.L z J → val β r z J = val (ExpGC.Bq wP a wLa wLb) r z J *
          (val (ExpGC.Bq wP a wLa wLb) (r ≫ (toUnit Xo.univ.t.G).left ≫ eSec Xo.univ.t.G) z J *
            val Xo.univ.t.PP.rig (r ≫ (toUnit Xo.univ.t.G).left) z J ^ (3 : ℤ))⁻¹ := by
  have hL := Xo.univ.t.PP.isLB
  have hrig := Xo.univ.t.PP.rigGen
  obtain ⟨β0, hβ0, hv0⟩ := ExpGC.exists_betaRaw wP hwP.1 a hbb wLa hwa wLb hwb
  have hg := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen Xo.univ.t.PP.L _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen Xo.univ.t.PP.L _ _ β0 hβ0 (eSec Xo.univ.t.G))
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen Xo.univ.t.PP.L _ _ _ _ _ _ hrig
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen Xo.univ.t.PP.L _ _ _ _ _ _ hrig hrig))
  obtain ⟨g0, hg0, hv1⟩ := exists_gen hL (φ' := (PEmpty.elim : PEmpty.{1} → ((𝟙_ (Over Xo.X)).left ⟶ Xo.univ.t.G.left)))
    (ε' := PEmpty.elim) (by
      intro U _ hU
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, betaφ, betaε,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, eSec_act, Category.comp_id, Finset.univ_unique, Finset.prod_singleton,
        Finset.univ_eq_empty, Finset.prod_empty]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      abel) _ hg
  have hB := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen Xo.univ.t.PP.L _ _ _ _ _ _ hβ0
    (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen Xo.univ.t.PP.L _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen Xo.univ.t.PP.L _ _ g0 hg0 (toUnit Xo.univ.t.G).left))
  obtain ⟨β, hβ, hv2⟩ := exists_gen hL (φ' := betaφ (Xo := Xo) a) (ε' := betaε) (by
      intro U _ hU
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_eq_empty, Finset.prod_empty,
        _root_.mul_one]) _ hB
  have hval : ∀ (Z : Scheme.{0}) (r : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
      Good Xo.univ.t.PP.L z J → val β r z J = val (ExpGC.Bq wP a wLa wLb) r z J *
        (val (ExpGC.Bq wP a wLa wLb) (r ≫ (toUnit Xo.univ.t.G).left ≫ eSec Xo.univ.t.G) z J *
          val Xo.univ.t.PP.rig (r ≫ (toUnit Xo.univ.t.G).left) z J ^ (3 : ℤ))⁻¹ := by
    intro Z r z J hJ
    rw [hv2 Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, hv1 Z _ z J hJ, val_mul hJ, val_pull hJ, val_mul hJ,
      val_mul hJ, hv0 Z r z J hJ, hv0 Z _ z J hJ, ← Category.assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  refine ⟨β, hβ, corr_of_val hL fun z J hJ => ?_, hval⟩
  rw [val_pull hJ, hval _ _ z J hJ, val_rigPow]
  simp only [Category.id_comp]
  rw [← Category.assoc (eSec Xo.univ.t.G), eSec_toUnit, Category.id_comp]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  abel

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinB
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open NumberField Module Formalism.MainNotions.ModuliIntegralCharts ComplexConjugate

variable {E : Type} [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

def comp (η : Y →ₗ[ℤ] ℝ) (σ : E →+* ℂ) (a : Y) : ℂ :=
  ∑ i, (η (RingOfIntegers.basis E i • a) : ℂ) * σ (ed E i)

theorem comp_add (η : Y →ₗ[ℤ] ℝ) (σ : E →+* ℂ) (a b : Y) :
    comp η σ (a + b) = comp η σ a + comp η σ b := by
  simp only [comp, smul_add, map_add (f := _), Complex.ofReal_add, add_mul, Finset.sum_add_distrib]

theorem comp_fadd (η ζ : Y →ₗ[ℤ] ℝ) (σ : E →+* ℂ) (a : Y) :
    comp (η + ζ) σ a = comp η σ a + comp ζ σ a := by
  simp only [comp, LinearMap.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]

theorem comp_fsmul (r : ℝ) (η : Y →ₗ[ℤ] ℝ) (σ : E →+* ℂ) (a : Y) :
    comp (r • η) σ a = r * comp η σ a := by
  simp only [comp, LinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

def compL (σ : E →+* ℂ) (a : Y) : (Y →ₗ[ℤ] ℝ) →ₗ[ℝ] ℂ where
  toFun η := comp η σ a
  map_add' η ζ := comp_fadd η ζ σ a
  map_smul' r η := by rw [comp_fsmul, RingHom.id_apply, Complex.real_smul]

theorem key_exp (u : 𝓞 E) (j : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    ∑ i, (((RingOfIntegers.basis E).repr (RingOfIntegers.basis E i * u) j : ℤ) : E) * ed E i =
      ed E j * (u : E) := by
  conv_rhs => rw [← (ed E).sum_repr (ed E j * (u : E))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr : (ed E).repr (ed E j * (u : E)) i
      = ((RingOfIntegers.basis E).repr (RingOfIntegers.basis E i * u) j : ℚ) := by
    rw [ed, LinearMap.BilinForm.dualBasis_repr_apply, ← ed, Algebra.traceForm_apply,
      ← tr_ed_int, integralBasis_apply]
    congr 1
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul]
    ring
  rw [hr, Algebra.smul_def]
  simp

theorem smul_expand (u : 𝓞 E) (i : Free.ChooseBasisIndex ℤ (𝓞 E)) (a : Y) :
    RingOfIntegers.basis E i • u • a = ∑ j, (RingOfIntegers.basis E).repr
      (RingOfIntegers.basis E i * u) j • (RingOfIntegers.basis E j • a) := by
  rw [← mul_smul]
  conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (RingOfIntegers.basis E i * u)]
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => smul_assoc _ _ _

theorem comp_smul (η : Y →ₗ[ℤ] ℝ) (σ : E →+* ℂ) (u : 𝓞 E) (a : Y) :
    comp η σ (u • a) = σ (u : E) * comp η σ a := by
  have hk : ∀ j, ∑ i, (((RingOfIntegers.basis E).repr (RingOfIntegers.basis E i * u) j : ℤ) : ℂ)
      * σ (ed E i) = σ (ed E j) * σ (u : E) := fun j => by
    have := congrArg σ (key_exp u j)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, map_mul, map_intCast] using this
  unfold comp
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [smul_expand u _ a, map_sum, map_zsmul, zsmul_eq_mul]
  push_cast
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_left_comm, mul_comm (σ (u : E)), ← hk j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sum_comp (η : Y →ₗ[ℤ] ℝ) (a : Y) : ∑ σ : E →+* ℂ, comp η σ a = (η a : ℂ) := by
  have htr : ∀ x : E, ∑ σ : E →+* ℂ, σ x = ((Algebra.trace ℚ E x : ℚ) : ℂ) := by
    intro x
    rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings ℂ]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ (fun σ => rfl)
  have h1 : ∑ i, (RingOfIntegers.basis E).repr 1 i • (RingOfIntegers.basis E i • a) = a := by
    simp_rw [← smul_assoc, ← Finset.sum_smul, (RingOfIntegers.basis E).sum_repr, one_smul]
  have htr1 : ∀ i, Algebra.trace ℚ E (ed E i) = ((RingOfIntegers.basis E).repr 1 i : ℚ) := fun i => by
    rw [← tr_ed_int]; simp
  unfold comp
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, htr, htr1]
  conv_rhs => rw [← h1]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, zsmul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_intCast, Rat.cast_intCast]
  exact Finset.sum_congr rfl fun i _ => by ring

def smulZ (u : 𝓞 E) : Y →ₗ[ℤ] Y where
  toFun y := u • y
  map_add' := smul_add u
  map_smul' n y := smul_comm u n y

theorem comp_pre (η : Y →ₗ[ℤ] ℝ) (σ : E →+* ℂ) (u : 𝓞 E) (a : Y) :
    comp (η ∘ₗ smulZ u) σ a = σ (u : E) * comp η σ a := by
  rw [← comp_smul]
  unfold comp
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [LinearMap.comp_apply, smulZ, LinearMap.coe_mk, AddHom.coe_mk]
  rw [smul_comm]


variable (E) in
def Pf (η ζ : Y →ₗ[ℤ] ℝ) (a c : Y) : ℝ :=
  (∑ σ : E →+* ℂ, (comp η σ a * conj (comp ζ σ c) + comp ζ σ a * conj (comp η σ c))).re

theorem Pf_add_left (η ζ : Y →ₗ[ℤ] ℝ) (a b c : Y) :
    Pf E η ζ (a + b) c = Pf E η ζ a c + Pf E η ζ b c := by
  simp only [Pf, comp_add, Complex.re_sum, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem Pf_add_right (η ζ : Y →ₗ[ℤ] ℝ) (a b c : Y) :
    Pf E η ζ a (b + c) = Pf E η ζ a b + Pf E η ζ a c := by
  simp only [Pf, comp_add, map_add (f := _), Complex.re_sum, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem Pf_symm (η ζ : Y →ₗ[ℤ] ℝ) (a c : Y) : Pf E η ζ a c = Pf E η ζ c a := by
  simp only [Pf, Complex.re_sum, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem Pf_comm (η ζ : Y →ₗ[ℤ] ℝ) (a c : Y) : Pf E η ζ a c = Pf E ζ η a c := by
  simp only [Pf, Complex.re_sum, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem Pf_fadd (η η' ζ : Y →ₗ[ℤ] ℝ) (a c : Y) :
    Pf E (η + η') ζ a c = Pf E η ζ a c + Pf E η' ζ a c := by
  simp only [Pf, comp_fadd, map_add (f := _), Complex.re_sum, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem Pf_fsmul (r : ℝ) (η ζ : Y →ₗ[ℤ] ℝ) (a c : Y) :
    Pf E (r • η) ζ a c = r * Pf E η ζ a c := by
  simp only [Pf, comp_fsmul, map_mul, Complex.conj_ofReal, Complex.re_sum, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem Pf_self (η : Y →ₗ[ℤ] ℝ) (a : Y) :
    Pf E η η a a = 2 * ∑ σ : E →+* ℂ, Complex.normSq (comp η σ a) := by
  simp only [Pf, Complex.re_sum, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem Pf_self_nonneg (η : Y →ₗ[ℤ] ℝ) (a : Y) : 0 ≤ Pf E η η a a := by
  rw [Pf_self]
  exact mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

section Forms

variable {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
include hcj

theorem Pf_bal (η ζ : Y →ₗ[ℤ] ℝ) (c c' : 𝓞 E) (h : (c' : E) = cj (c : E)) (a b : Y) :
    Pf E η ζ (c • a) b = Pf E η ζ a (c' • b) := by
  have hs : ∀ σ : E →+* ℂ, conj (σ (c' : E)) = σ (c : E) := fun σ => by
    rw [h, hcj]; simp
  simp only [Pf, comp_smul, map_mul, hs]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => by ring


omit hcj in
variable (E) in
def PfB (η ζ : Y →ₗ[ℤ] ℝ) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ :=
  (AddMonoidHom.mk' (fun a => (AddMonoidHom.mk' (fun c => Pf E η ζ a c)
      (Pf_add_right η ζ a)).toIntLinearMap)
    (fun a b => LinearMap.ext fun c => Pf_add_left η ζ a b c)).toIntLinearMap

theorem PfB_mem (η ζ : Y →ₗ[ℤ] ℝ) : PfB E η ζ ∈ SymB cj Y :=
  ⟨fun a b => Pf_symm η ζ a b, fun c c' h a b => Pf_bal hcj η ζ c c' h a b⟩

def Pm : (Y →ₗ[ℤ] ℝ) →ₗ[ℝ] (Y →ₗ[ℤ] ℝ) →ₗ[ℝ] SymB cj Y :=
  LinearMap.mk₂ ℝ (fun η ζ => ⟨PfB E η ζ, PfB_mem hcj η ζ⟩)
    (fun η η' ζ => Subtype.ext (LinearMap.ext₂ fun a c => Pf_fadd η η' ζ a c))
    (fun r η ζ => Subtype.ext (LinearMap.ext₂ fun a c => Pf_fsmul r η ζ a c))
    (fun η ζ ζ' => Subtype.ext (LinearMap.ext₂ fun a c => by
      show Pf E η (ζ + ζ') a c = Pf E η ζ a c + Pf E η ζ' a c
      rw [Pf_comm, Pf_fadd, Pf_comm η ζ, Pf_comm η ζ']))
    (fun r η ζ => Subtype.ext (LinearMap.ext₂ fun a c => by
      show Pf E η (r • ζ) a c = r * Pf E η ζ a c
      rw [Pf_comm, Pf_fsmul, Pf_comm η ζ]))

theorem Pm_apply (η ζ : Y →ₗ[ℤ] ℝ) (a c : Y) :
    ((Pm hcj η ζ : SymB cj Y) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = Pf E η ζ a c := rfl

theorem Pm_psd (η : Y →ₗ[ℤ] ℝ) (a : Y) :
    0 ≤ ((Pm hcj η η : SymB cj Y) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a :=
  Pf_self_nonneg η a

theorem Pm_ne_zero {η : Y →ₗ[ℤ] ℝ} (hη : η ≠ 0) : Pm hcj η η ≠ 0 := by
  intro h0
  apply hη
  ext a
  have hP : Pf E η η a a = 0 := by
    have := congrArg (fun β : SymB cj Y => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) h0
    simpa [Pm_apply] using this
  rw [Pf_self] at hP
  have hsum : ∑ σ : E →+* ℂ, Complex.normSq (comp η σ a) = 0 := by linarith
  have hc : ∀ σ : E →+* ℂ, comp η σ a = 0 := fun σ =>
    Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Complex.normSq_nonneg _)).mp hsum σ (Finset.mem_univ σ))
  have := sum_comp (E := E) η a
  simp only [hc, Finset.sum_const_zero] at this
  simp only [LinearMap.zero_apply]
  exact_mod_cast this.symm


omit hcj in
theorem Pf_skew (θ : 𝓞 E) (hθ : ∀ σ : E →+* ℂ, star (σ (θ : E)) = -σ (θ : E))
    (η ζ : Y →ₗ[ℤ] ℝ) (a c : Y) :
    Pf E (η ∘ₗ smulZ θ) ζ a c = -Pf E η (ζ ∘ₗ smulZ θ) a c := by
  have hs : ∀ σ : E →+* ℂ, conj (σ (θ : E)) = -σ (θ : E) := hθ
  simp only [Pf, comp_pre, map_mul, hs]
  rw [← Complex.neg_re, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => by ring

end Forms

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts

def PhiCSpanStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] (w₀ : 𝓞 E), (w₀ : E) + cj w₀ = 1 →
    ∀ (β : SymB cj Y), (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) →
    ∀ (k : ℕ) (x : Fin k → Y),
      (∀ y : Y, ∃ n : ℕ, 0 < n ∧ n • y ∈ Submodule.span (𝓞 E) (Set.range x)) →
      phiC cj β ≤ ∑ b, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x b) (x b)

def PhiCMinimaStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) → (∃ z : E, cj z ≠ z) →
    ∀ (w₀ : 𝓞 E), (w₀ : E) + cj w₀ = 1 →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
      (β : SymB cj Y),
      (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ Y),
        (Matrix.of fun i j => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b i) (b j)).PosDef) →
      ∃ v : Fin (Module.finrank ℤ Y) → Y, LinearIndependent ℤ v ∧
        ∀ i, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (v i) (v i) / 2 ≤
          (|(NumberField.discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) /
              (2 * Module.finrank ℚ E) * (Module.finrank ℤ Y : ℝ) ^ 2 * phiC cj β

def PhiCTieStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y]
    [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (l : SymB cj Y →ₗ[ℝ] ℝ),
    (∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) →
    ∃ (m : ℕ) (x x' : Fin m → Y), ∀ β : SymB cj Y,
      l β = ∑ i, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x' i)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.RoundingSum
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.RoundingSumAlt

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ}

theorem Q_nonneg (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (χ : D.toPre.X) : 0 ≤ Q χ := by
  by_cases hχ : χ = 0
  · rw [hχ, Q_zero hϖ (D := D) (Q := Q) (hQ := hQ)]
  · exact le_trans zero_le_one (Q_pos hϖ (D := D) (Q := Q) (hQ := hQ) hχ)

end Formalism.MainNotions.ModuliIntegralCharts.H1.RoundingSumAlt
end
end

