module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.Bundle0001
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.DimFormCOfThree
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem orbitCount : OrbitCount := by
  intro G _ Γ K n t A N hA hAN hK hΓ
  classical
  have key : ∀ j i, DoubleCoset.mk Γ K (t i) = DoubleCoset.mk Γ K (t j) →
      ∃ γ ∈ Γ, ∃ κ ∈ K, t j = γ * t i * κ := fun j i h => (@DoubleCoset.eq _ _ Γ K (t i) (t j)).mp h
  have hcard : (Finset.univ : Finset (Fin n)).card ≤
      N * (Finset.univ.image fun i => DoubleCoset.mk Γ K (t i)).card := by
    apply Finset.card_le_mul_card_image
    intro a ha
    obtain ⟨i0, -, rfl⟩ := Finset.mem_image.mp ha
    let g : Fin n → G := fun j =>
      if h : DoubleCoset.mk Γ K (t i0) = DoubleCoset.mk Γ K (t j) then (key j i0 h).choose else 1
    calc (Finset.univ.filter fun j => DoubleCoset.mk Γ K (t j) = DoubleCoset.mk Γ K (t i0)).card
        ≤ hA.toFinset.card := by
          apply Finset.card_le_card_of_injOn g
          · intro j hj
            have hj' : DoubleCoset.mk Γ K (t i0) = DoubleCoset.mk Γ K (t j) :=
              ((Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2).symm
            obtain ⟨hγ, κ, hκ, he⟩ := (key j i0 hj').choose_spec
            rw [Finset.mem_coe, Set.Finite.mem_toFinset]
            simp only [g, dif_pos hj']
            exact hΓ i0 j _ hγ κ hκ he
          · intro j hj j' hj' hgg
            have h1 : DoubleCoset.mk Γ K (t i0) = DoubleCoset.mk Γ K (t j) :=
              ((Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2).symm
            have h2 : DoubleCoset.mk Γ K (t i0) = DoubleCoset.mk Γ K (t j') :=
              ((Finset.mem_filter.mp (Finset.mem_coe.mp hj')).2).symm
            obtain ⟨-, κ, hκ, he⟩ := (key j i0 h1).choose_spec
            obtain ⟨-, κ', hκ', he'⟩ := (key j' i0 h2).choose_spec
            simp only [g, dif_pos h1, dif_pos h2] at hgg
            apply hK
            rw [he, he', hgg]
            have e1 : ((key j' i0 h2).choose * t i0 * κ)⁻¹ * ((key j' i0 h2).choose * t i0 * κ') = κ⁻¹ * κ' := by
              group
            rw [e1]
            exact K.mul_mem (K.inv_mem hκ) hκ'
      _ ≤ N := by
          rw [← Set.ncard_eq_toFinset_card A hA, ← Nat.card_coe_set_eq]
          exact hAN
  have e : Nat.card (Set.range fun i => DoubleCoset.mk Γ K (t i)) =
      (Finset.univ.image fun i => DoubleCoset.mk Γ K (t i)).card := by
    first
      | rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_range]
      | simp [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
  rw [e]
  simpa using hcard

theorem kuStab : KuStab := by
  intro D X u hK h κ
  obtain ⟨⟨κ, hκ'⟩, hκ⟩ := κ
  have hk : (X.xu u)⁻¹ * κ * X.xu u ∈ X.K2 := hκ
  show latS X u (h * κ) = latS X u h
  have h2 : ((X.xu u)⁻¹ * κ * X.xu u)⁻¹ ∈ X.K2 := hK.2.2.1 _ hk
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.K2 K2set at h2
  have hs : ∀ x, x ∈ X.B.I.Lf ↔
      (X.B.I.fmat ((X.xu u)⁻¹ * κ * X.xu u)⁻¹).mulVec x ∈ X.B.I.Lf := h2.1
  have he : (h * κ * X.xu u)⁻¹ = ((X.xu u)⁻¹ * κ * X.xu u)⁻¹ * (h * X.xu u)⁻¹ := by
    group
  have hm : X.B.I.fmat (((X.xu u)⁻¹ * κ * X.xu u)⁻¹ * (h * X.xu u)⁻¹) =
      X.B.I.fmat ((X.xu u)⁻¹ * κ * X.xu u)⁻¹ * X.B.I.fmat (h * X.xu u)⁻¹ := rfl
  ext y
  simp only [latS, Set.mem_setOf_eq]
  rw [he, hm, ← Matrix.mulVec_mulVec]
  exact (hs _).symm

theorem dimFormC_of_three (hT : Transport) (hB : StabBound) (hI : IndexGe) : Formalism.L2.SG.KappaOffDiagonal.DimFormC :=
  dimFormC_of_steps orbitCount hT kuStab hB hI

end PI.UnitaryDimensionFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.MemMLOfInAt
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  PI.UnitaryDimensionFormula.unitaryCongruence

namespace PI.UnitaryDimensionFormula.NormCutK

section Par

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hform_mulVec' {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J M : Matrix n n A) (hM : Formalism.UG.cT σ M * J * M = J) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ J x y := by
  have hdot : ∀ x y : n → A, Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hσ : (fun i => σ ((M *ᵥ x) i)) = (M.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [mulVec, dotProduct, map_sum, map_mul]
  rw [hdot, hdot, hσ, ← vecMul_transpose, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← Matrix.mul_assoc]
  rw [show (M.map σ)ᵀ * J * M = J from hM]

theorem hA_unit (g : X.B.I.Gf) (x y : VA X.B.I) :
    hA X.B.I (X.B.I.fmat g *ᵥ x) (X.B.I.fmat g *ᵥ y) = hA X.B.I x y :=
  hform_mulVec' _ _ _ g.2 x y

theorem hA_adj (g : X.B.I.Gf) (x y : VA X.B.I) :
    hA X.B.I x (X.B.I.fmat g *ᵥ y) = hA X.B.I (X.B.I.fmat g⁻¹ *ᵥ x) y := by
  conv_lhs => rw [← hA_unit X g⁻¹ x (X.B.I.fmat g *ᵥ y)]
  rw [Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec]

theorem mem_mL_of_InAt {d : VA X.B.I} (hd : d ∈ X.B.I.Lf) (h : InAt X.B.I X.B.g X.B.g d) :
    d ∈ mL X.B.I X.B.g := by
  obtain ⟨c, hc, hcd⟩ := h
  have hb : ((c : ℤ) * Nat.gcdA c X.B.g + (X.B.g : ℤ) * Nat.gcdB c X.B.g) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hc.gcd_eq_one]; rfl
  have e : d = ((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • d) +
      ((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • d) := by
    rw [smul_smul, smul_smul, ← add_smul]
    have : ((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
        ((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = 1 := by
      have := congrArg (fun z : ℤ => (z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) hb
      push_cast at this
      linear_combination this
    rw [this, one_smul]
  rw [e]
  have hint : ∀ z : ℤ, ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ IntAf X.B.I.F X.B.I.E := fun z => intCast_mem _ z
  have sm : ∀ (z : ℤ) (w : VA X.B.I), w ∈ mL X.B.I X.B.g →
      ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) • w ∈ mL X.B.I X.B.g := fun z w hw => by
    have : ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) • w = (⟨_, hint z⟩ : IntAf X.B.I.F X.B.I.E) • w := rfl
    rw [this]; exact Submodule.smul_mem _ _ hw
  exact add_mem (sm _ _ hcd) (sm _ _ (smul_mem_mL X.B.I hd))

theorem mem_Mo_eb {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) v))
    (hz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 v)) (hb : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bw l) v)) :
    v ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hd := dual_coords X hv
  have e : v = (v - repr0 X v) + repr0 X v := by abel
  rw [e]
  refine add_mem (mL_Mo X.B.I hd) ?_
  have spn : ∀ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (w : VA X.B.I), c ∈ IntAf X.B.I.F X.B.I.E →
      w ∈ Set.range X.e0 ∪ Set.range X.bw → c • w ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw) :=
    fun c w hc hw => by
      have : c • w = (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) • w := rfl
      rw [this]; exact Submodule.smul_mem _ _ (sub_Mo X.B.I hw)
  unfold repr0
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact sum_mem fun a _ => spn _ _ (hA_int X.B.I (hF a) hv) (Or.inl ⟨a, rfl⟩)
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (he a) (hF a))
  · exact mL_Mo X.B.I (Z_smul_mL X hz hZ)
  · exact sum_mem fun l _ => spn _ _ (hA_int X.B.I (hBd l) hv) (Or.inr ⟨l, rfl⟩)
  · exact sum_mem fun l _ => mL_Mo X.B.I (Z_smul_mL X (hb l) (hBd l))

def Par (x : X.B.I.Gf) : Prop :=
  x ∈ X.B.I.Kset ∧ (∀ a, X.B.I.fmat x *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (Set.range X.e0)) ∧
    ∀ j, X.B.I.fmat x *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw)

def Good (x : X.B.I.Gf) : Prop := Par X x ∧ Par X x⁻¹

theorem par_one : Par X 1 := by
  refine ⟨K_one X.B.I, fun a => ?_, fun j => ?_⟩
  · rw [show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]; exact sub_Mo X.B.I ⟨a, rfl⟩
  · rw [show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]; exact sub_Mo X.B.I (Or.inr ⟨j, rfl⟩)

theorem par_mul {x y : X.B.I.Gf} (hx : Par X x) (hy : Par X y) : Par X (x * y) := by
  refine ⟨K_mul X.B.I hx.1 hy.1, fun a => ?_, fun j => ?_⟩
  · rw [fmat_mul, ← Matrix.mulVec_mulVec]
    refine pres X.B.I hx.1 X.B.g (Set.range X.e0) _ (sub_Mo X.B.I) ?_ (mL_Mo X.B.I) _ (hy.2.1 a)
    rintro _ ⟨b, rfl⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (hx.2.1 b) (sub_Mo X.B.I ⟨b, rfl⟩)
  · rw [fmat_mul, ← Matrix.mulVec_mulVec]
    refine pres X.B.I hx.1 X.B.g (Set.range X.e0 ∪ Set.range X.bw) _ (sub_Mo X.B.I) ?_ (mL_Mo X.B.I) _ (hy.2.2 j)
    rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_mem (Mo_mono X.B.I Set.subset_union_left (hx.2.1 b)) (sub_Mo X.B.I (Or.inl ⟨b, rfl⟩))
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_mem (hx.2.2 l) (sub_Mo X.B.I (Or.inr ⟨l, rfl⟩))

theorem good_one : Good X 1 := ⟨par_one X, by simpa using par_one X⟩

theorem good_mul {x y : X.B.I.Gf} (hx : Good X x) (hy : Good X y) : Good X (x * y) :=
  ⟨par_mul X hx.1 hy.1, by rw [_root_.mul_inv_rev]; exact par_mul X hy.2 hx.2⟩

variable {X} (TR : TypedRed X)

theorem leviM_mul_par {x y : X.B.I.Gf} (hx : Par X x) (hy : Par X y) (v : TR.Pl) :
    leviM TR (x * y) v = leviM TR x v * leviM TR y v :=
  leviM_mul TR hx.1 hy.1 hy.2.2 hx.2.1 v

theorem leviM_one (v : TR.Pl) : leviM TR 1 v = 1 := by
  ext i j
  have hbw : ∀ j, X.bw j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).1
  have hbwd : ∀ j, X.bwd j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).2
  simp only [leviM, show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]
  have hI := hA_int X.B.I (hbwd i) (hbw j)
  rw [resT_of_mem TR v hI]
  have hZ := X.bw_dual i j
  have hIt : (if i = j then X.ew else 0) ∈ IntAf X.B.I.F X.B.I.E := by
    split_ifs
    · exact X.ew_int
    · exact zero_mem _
  have e : (⟨_, hI⟩ : IntAf X.B.I.F X.B.I.E) = ⟨_, sub_mem hI hIt⟩ + ⟨_, hIt⟩ := by
    apply Subtype.ext; simp
  rw [e, map_add (f := _), res_eq_zero_of_Z TR v _ hZ, zero_add]
  by_cases h : i = j
  · subst h
    simp only [if_true, Matrix.one_apply_eq]
    have e2 : (⟨X.ew, X.ew_int⟩ : IntAf X.B.I.F X.B.I.E) = ⟨X.ew * (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
        (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int (one_mem _)⟩ := by apply Subtype.ext; simp
    have := TR.res_ew v 1
    simp only [OneMemClass.coe_one] at this
    convert this using 2
    exact (map_one (TR.res v)).symm
  · simp only [h, if_false, Matrix.one_apply_ne h]
    exact map_zero (TR.res v) |>.symm ▸ (by congr 1)

end Par

end PI.UnitaryDimensionFormula.NormCutK
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.Transp
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem tr_repr_eq (y : (VS D).V) (i : Fin X.B.I.n) : X.bas.repr y i = X.ιE (X.crd y i) := by
  exact (X.ιE.apply_symm_apply (X.bas.repr y i)).symm

theorem tr_crd_injective : Function.Injective X.crd := by
  intro a b h
  apply X.bas.repr.injective
  ext i
  rw [tr_repr_eq X a i, tr_repr_eq X b i, h]

def trLin (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  Matrix.toLin X.bas X.bas (M.map X.ιE)

theorem tr_crd_lin (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.crd (trLin X M y) = M *ᵥ X.crd y := by
  have h := LinearMap.toMatrix_mulVec_repr X.bas X.bas (Matrix.toLin X.bas X.bas (M.map X.ιE)) y
  rw [LinearMap.toMatrix_toLin] at h
  funext i
  apply X.ιE.injective
  rw [← tr_repr_eq]
  show X.bas.repr (Matrix.toLin X.bas X.bas (M.map X.ιE) y) i = _
  rw [← h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, tr_repr_eq]

theorem tr_lin_mul (M N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    (trLin X M).comp (trLin X N) = trLin X (M * N) := by
  have hm : (M * N).map X.ιE = M.map X.ιE * N.map X.ιE := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, map_sum, map_mul]
  unfold trLin
  rw [hm, Matrix.toLin_mul X.bas X.bas X.bas]

theorem tr_lin_one : trLin X 1 = LinearMap.id := by
  unfold trLin
  rw [Matrix.map_one _ (map_zero X.ιE) (map_one X.ιE), Matrix.toLin_one]

def trEquiv (M : GL (Fin X.B.I.n) X.B.I.E) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (trLin X (M : Matrix _ _ _)) (trLin X ((M⁻¹ : GL _ _) : Matrix _ _ _))
    (by rw [tr_lin_mul, Units.mul_inv, tr_lin_one])
    (by rw [tr_lin_mul, Units.inv_mul, tr_lin_one])

theorem tr_crd (M : GL (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.crd (trEquiv X M y) = (M : Matrix _ _ _) *ᵥ X.crd y := tr_crd_lin X _ y

theorem tr_af_nontrivial (F : Type) [Field F] [NumberField F] : Nontrivial (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.mp (NumberField.RingOfIntegers.not_isField F)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨p, hp, hp0⟩
  haveI : Nonempty (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) := ⟨v⟩
  first
    | infer_instance
    | exact (RestrictedProduct.evalRingHom _ v).domain_nontrivial
    | exact ⟨⟨0, 1, fun h => zero_ne_one (congrArg (fun x => x.1 v) h)⟩⟩

attribute [local instance] tr_af_nontrivial

theorem tr_star (a : X.B.I.E) : star (X.ιE a) = X.ιE (star a) :=
  (Formalism.BasicNotions.bridge_star_holds D.R D.host _).trans (X.ιE_conj a).symm

theorem tr_hT (x y : (VS D).V) :
    (VS D).hT x y = X.ιE (star (X.crd x) ⬝ᵥ (X.B.I.J *ᵥ X.crd y)) := by
  conv_lhs => rw [← X.bas.sum_repr x, ← X.bas.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, starRingEnd_apply, tr_repr_eq, tr_star, ← X.J_eq, dotProduct, Matrix.mulVec,
    Pi.star_apply, map_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem tr_isom (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    trEquiv X M ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
  have hM' : Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * X.B.I.J *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J := hM
  have hH : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ =
      Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) := by
    ext i j
    rfl
  show ∀ a b, (VS D).hT (trEquiv X M a) (trEquiv X M b) = (VS D).hT a b
  intro a b
  rw [tr_hT, tr_hT, tr_crd, tr_crd]
  congr 1
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hH, hM']

theorem transport_holds : Transport := by
  intro D X u γ
  have hG : (γ : X.B.I.GA) ∈ X.B.I.GFset := (Subgroup.mem_inf.1 γ.2).1
  obtain ⟨M, hM, -, hf⟩ := hG
  have hH : ∀ y ∈ fixSet X u, X.B.I.fmat (iotaF X u γ : X.B.I.Gf) *ᵥ incl X.B.I y = incl X.B.I y :=
    (iotaF X u γ).2
  have hcoe : ((iotaF X u γ : Hfin X u) : X.B.I.Gf) = (γ : X.B.I.GA).2 := rfl
  have hinc : ∀ v, X.B.I.fmat (γ : X.B.I.GA).2 *ᵥ incl X.B.I v =
      incl X.B.I ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ v) := by
    intro v
    rw [hf]
    funext i
    exact (RingHom.map_mulVec _ _ _ i).symm
  have hfixc : ∀ y ∈ fixSet X u, (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y = y := by
    intro y hy
    have h1 := hH y hy
    rw [hcoe, hinc] at h1
    funext i
    exact Formalism.UG.P.inclE_injective _ _ _ (congrFun h1 i)
  have hfix : ∀ y, X.crd y ∈ fixSet X u → trEquiv X M y = y := by
    intro y hy
    apply tr_crd_injective X
    rw [tr_crd, hfixc _ hy]
  refine ⟨trEquiv X M, ⟨tr_isom X M hM, fun j => ?_, ?_⟩, fun h => ?_⟩
  · show Submodule.map _ (Submodule.span _ _) = Submodule.span _ _
    rw [Submodule.map_span, Set.image_image, X.Fu_e]
    congr 1
    apply Set.image_congr
    intro a _
    exact hfix _ (Or.inl (Or.inl ⟨a, rfl⟩))
  · rw [X.flagZVector]
    exact hfix _ (Or.inr rfl)
  · ext y
    have key : X.B.I.fmat ((iotaF X u γ : X.B.I.Gf))⁻¹ *ᵥ incl X.B.I (X.crd y) =
        incl X.B.I (X.crd ((trEquiv X M).symm y)) := by
      have e1 : incl X.B.I (X.crd y) =
          X.B.I.fmat (iotaF X u γ : X.B.I.Gf) *ᵥ incl X.B.I (X.crd ((trEquiv X M).symm y)) := by
        rw [hcoe, hinc, ← tr_crd, LinearEquiv.apply_symm_apply]
      rw [e1, Matrix.mulVec_mulVec]
      have e2 : X.B.I.fmat ((iotaF X u γ : X.B.I.Gf))⁻¹ * X.B.I.fmat (iotaF X u γ : X.B.I.Gf) =
          X.B.I.fmat (((iotaF X u γ : X.B.I.Gf))⁻¹ * (iotaF X u γ : X.B.I.Gf)) := rfl
      rw [e2, inv_mul_cancel]
      exact Matrix.one_mulVec _
    have e : ((iotaF X u γ : X.B.I.Gf) * h * X.xu u)⁻¹ = (h * X.xu u)⁻¹ * (iotaF X u γ : X.B.I.Gf)⁻¹ := by
      group
    rw [LinearEquiv.image_eq_preimage_symm]
    simp only [latS, Set.mem_ofPred_eq, Set.mem_preimage]
    rw [e]
    have ef : X.B.I.fmat ((h * X.xu u)⁻¹ * (iotaF X u γ : X.B.I.Gf)⁻¹) =
        X.B.I.fmat (h * X.xu u)⁻¹ * X.B.I.fmat ((iotaF X u γ : X.B.I.Gf))⁻¹ := rfl
    rw [ef, ← Matrix.mulVec_mulVec, key]

end PI.UnitaryDimensionFormula
end
end

