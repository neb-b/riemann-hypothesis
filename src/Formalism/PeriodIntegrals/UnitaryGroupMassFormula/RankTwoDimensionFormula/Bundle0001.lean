module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.GammaOneEqProd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.FlagLevelCharacterEqPsiDivN

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.DimFormCOfSteps
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def latS {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (h : X.B.I.Gf) : Set (VS D).V :=
  {y | (X.B.I.fmat (h * X.xu u)⁻¹).mulVec (incl X.B.I (X.crd y)) ∈ X.B.I.Lf}

theorem lamOf_eq_latS {D : D7} {X : HidaSetting D} {u : D.what₂.Word}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (ρ : cs.Cl) :
    ((cs.lamOf ρ : Submodule (𝓞 D.host.E) (VS D).V) : Set (VS D).V) = latS X u (cs.h ρ : X.B.I.Gf) := by
  ext y
  exact cs.lat_eq ρ y

def OrbitCount : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (n : ℕ) (t : Fin n → G) (A : Set G) (N : ℕ),
    A.Finite → Nat.card A ≤ N →
    (∀ i j, (t i)⁻¹ * t j ∈ K → i = j) →
    (∀ i j, ∀ γ ∈ Γ, ∀ κ ∈ K, t j = γ * t i * κ → γ ∈ A) →
    n ≤ N * Nat.card (Set.range fun i => DoubleCoset.mk Γ K (t i))

def Transport : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ : Gam X u), ∃ g ∈ stabF D (X.Fu u),
    ∀ h : X.B.I.Gf, latS X u ((iotaF X u γ : X.B.I.Gf) * h) = g '' latS X u h

def KuStab : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (h : X.B.I.Gf) (κ : Ku X u hK),
    latS X u (h * ((κ : Hfin X u) : X.B.I.Gf)) = latS X u h

def StabBound : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    ∀ Λ ∈ Y.what₂ u, (autLz D (X.Fu u) Λ).Finite →
      ∃ A : Set (Hfin X u), A.Finite ∧ Nat.card A ≤ Nat.card (autLz D (X.Fu u) Λ) ∧
        ∀ h h' : Hfin X u, latS X u (h : X.B.I.Gf) = (Λ : Set (VS D).V) →
          latS X u (h' : X.B.I.Gf) = (Λ : Set (VS D).V) →
          ∀ γ ∈ (iotaF X u).range, ∀ κ ∈ Ku X u Y.hK, h' = γ * h * κ → γ ∈ A

def IndexGe : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    ∀ Λ ∈ Y.what₂ u, ∃ (n : ℕ) (t : Fin n → Hfin X u), Gam1 Y.TR ≤ (n : ℝ) ∧
      (∀ i, latS X u (t i : X.B.I.Gf) = (Λ : Set (VS D).V)) ∧
      ∀ i j, (t i)⁻¹ * t j ∈ Ku X u Y.hK → i = j

theorem fibreCover (hT : Transport) (hS : KuStab) {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ Y.what₂ u) (h : Hfin X u)
    (hh : latS X u (h : X.B.I.Gf) = (Λ : Set (VS D).V)) :
    ∃ ρ ∈ fib (Y.cs u) Λ, DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) h =
      DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ) := by
  obtain ⟨ρ, ⟨γ, κ, hρ⟩, -⟩ := Y.colReps u h
  refine ⟨ρ, ?_, ?_⟩
  · simp only [fib]
    have h1 : latS X u (h : X.B.I.Gf) =
        latS X u ((iotaF X u γ : X.B.I.Gf) * ((Y.cs u).h ρ : X.B.I.Gf)) := by
      rw [hρ, Subgroup.coe_mul, hS D X u Y.hK _ κ, Subgroup.coe_mul]
    obtain ⟨g, hg, hgt⟩ := hT D X u γ
    have h2 : (Λ : Set (VS D).V) = g '' ((((Y.cs u).lamOf ρ) : Submodule (𝓞 D.host.E) (VS D).V) : Set (VS D).V) := by
      rw [← hh, h1, hgt, lamOf_eq_latS]
    have hR := Y.rowsOK u
    unfold IsRowReps at hR
    obtain ⟨hRl, hU⟩ := hR
    obtain ⟨Λ0, -, huniq⟩ := hU Λ (hRl Λ hΛ)
    have e1 : Λ = Λ0 := huniq Λ ⟨hΛ, 1, by simp [stabF], by ext; simp [Formalism.HermitianLatticesTheory.gmap]⟩
    have e2 : (Y.cs u).lamOf ρ = Λ0 := by
      refine huniq _ ⟨(Y.cs u).lam_mem ρ, g, hg, ?_⟩
      apply SetLike.coe_injective
      rw [h2]
      simp [Formalism.HermitianLatticesTheory.gmap]
    simpa using e2.trans e1.symm
  · exact ((@DoubleCoset.eq _ _ _ _ _ _).mpr ⟨iotaF X u γ, MonoidHom.mem_range.mpr ⟨γ, rfl⟩, κ, κ.2, hρ⟩).symm

theorem fibreBound_of (hO : OrbitCount) (hT : Transport) (hS : KuStab) (hB : StabBound) (hI : IndexGe) :
    FibreBound := by
  intro D X Y u hC Λ hΛ
  obtain ⟨n, t, hn, ht, hd⟩ := hI D X Y u hC Λ hΛ
  unfold wRow
  by_cases hN0 : Nat.card (autLz D (X.Fu u) Λ) = 0
  · simp [hN0]
  have hfin : (autLz D (X.Fu u) Λ).Finite :=
    Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hN0)
  obtain ⟨A, hAf, hAc, hA⟩ := hB D X Y u hC Λ hΛ hfin
  have horb := hO (Hfin X u) (iotaF X u).range (Ku X u Y.hK) n t A _ hAf hAc hd
    (fun i j γ hγ κ hκ he => hA (t i) (t j) (ht i) (ht j) γ hγ κ hκ he)
  have hsub : Set.range (fun i => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) (t i)) ⊆
      (((fib (Y.cs u) Λ).image
        (fun ρ => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ)) : Finset _) : Set _) := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨ρ, hρ, he⟩ := fibreCover hT hS Y u Λ hΛ (t i) (ht i)
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ρ, hρ, he.symm⟩)
  have hc : Nat.card (Set.range (fun i => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) (t i))) ≤
      (fib (Y.cs u) Λ).card := by
    calc _ ≤ Nat.card (((fib (Y.cs u) Λ).image
          (fun ρ => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ)) : Finset _) : Set _) :=
          Nat.card_mono (Finset.finite_toSet _) hsub
      _ = ((fib (Y.cs u) Λ).image
          (fun ρ => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ))).card := by
          rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
      _ ≤ _ := Finset.card_image_le
  have hNpos : (0 : ℝ) < (Nat.card (autLz D (X.Fu u) Λ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hN0
  have key : (n : ℝ) ≤ (Nat.card (autLz D (X.Fu u) Λ) : ℝ) * ((fib (Y.cs u) Λ).card : ℝ) := by
    exact_mod_cast horb.trans (Nat.mul_le_mul_left _ hc)
  calc Gam1 Y.TR * ((Nat.card (autLz D (X.Fu u) Λ) : ℝ))⁻¹
      ≤ (n : ℝ) * ((Nat.card (autLz D (X.Fu u) Λ) : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hn (inv_nonneg.mpr hNpos.le)
    _ ≤ ((fib (Y.cs u) Λ).card : ℝ) := by
        rw [← div_eq_mul_inv, div_le_iff₀ hNpos]
        linarith [key]

theorem dimFormC_of_steps (hO : OrbitCount) (hT : Transport) (hS : KuStab) (hB : StabBound) (hI : IndexGe) :
    Formalism.L2.SG.KappaOffDiagonal.DimFormC :=
  dimFormC_of (fibreBound_of hO hT hS hB hI)

end PI.UnitaryDimensionFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.DualBetaReferenceCongruence
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  PI.UnitaryDimensionFormula.unitaryCongruence

namespace PI.UnitaryDimensionFormula.NormCutK

section LeviMul

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem resT_of_mem (v : TR.Pl) {z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hz : z ∈ IntAf X.B.I.F X.B.I.E) :
    resT TR v z = TR.res v ⟨z, hz⟩ := by
  unfold resT; rw [dite_eq_left hz]

theorem res_eq_zero_of_Z (v : TR.Pl) {z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hz : z ∈ IntAf X.B.I.F X.B.I.E)
    (hZ : ZMod' X.B.I X.B.g z) : TR.res v ⟨z, hz⟩ = 0 :=
  (TR.res_ker ⟨z, hz⟩).2 (Z_smul X.B.I X.B.g X.ew_int hZ) v

def PhiSub (x : X.B.I.Gf) (i : Fin D.R.k) : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) where
  carrier := {z | ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
    ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z)}
  add_mem' {z w} hz hw := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ (z + w)) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (z + w))
    have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ (z + w)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (z + w) =
        (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z) +
        (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ w) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) w) := by
      simp only [Matrix.mulVec_add, hA_add_right, mul_add, Finset.sum_add_distrib]; ring
    rw [e]; exact Z_add X.B.I X.B.g hz hw
  zero_mem' := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ 0) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) 0)
    have h0 : ∀ u : VA X.B.I, hA X.B.I u 0 = 0 := fun u => (hL X.B.I u).map_zero
    simp only [Matrix.mulVec_zero, h0, mul_zero, Finset.sum_const_zero, sub_zero]
    exact Z_zero X.B.I X.B.g
  smul_mem' c z hz := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z)) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z))
    have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z) =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z) := by
      simp only [Matrix.mulVec_smul, hA_smul_right, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]; exact Z_smul X.B.I X.B.g c.2 hz

theorem dual_beta_reference_congruence (i : Fin D.R.k) (a : Fin D.R.rS) : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.e0 a)) := by
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g ((X.weightVectorsIntegral i).2.2 a).2.2.1

theorem leviM_mul {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hy : y ∈ X.B.I.Kset)
    (hyb : ∀ j, X.B.I.fmat y *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw))
    (hxe : ∀ a, X.B.I.fmat x *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (Set.range X.e0)) (v : TR.Pl) :
    leviM TR (x * y) v = leviM TR x v * leviM TR y v := by
  have hbw : ∀ j, X.bw j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).1
  have hbwd : ∀ j, X.bwd j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).2
  have he0 : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).1

  have key : ∀ i, Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw) ≤ PhiSub x i := by
    intro i
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro z (⟨a, rfl⟩ | ⟨m, rfl⟩)
      · show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.e0 a) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.e0 a))
        refine Z_sub X.B.I X.B.g ?_ (Z_sum X.B.I X.B.g _ _ fun l _ =>
          Z_smul X.B.I X.B.g (hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))) (dual_beta_reference_congruence l a))
        have hQ : Mo X.B.I X.B.g (Set.range X.e0) ≤ Qs X.B.I X.B.g (X.bwd i) :=
          sup_le (Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact dual_beta_reference_congruence i b)) (mL_Qs X.B.I X.B.g (hbwd i))
        exact hQ (hxe a)
      · show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.bw m))
        have hw : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) = X.ew * hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) := by
          conv_lhs => rw [X.bw_w m, Matrix.mulVec_smul, hA_smul_right]
        have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) -
            ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.bw m) =
            (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) - hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) * X.ew) -
            ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) *
              (hA X.B.I (X.bwd l) (X.bw m) - if l = m then X.ew else 0) := by
          simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
            if_true]
          ring
        have e2 : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) - hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) * X.ew = 0 := by
          rw [hw]
          have := X.ew_idem
          linear_combination (-(hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m))) * this
        rw [e, e2, zero_sub]
        have := Z_sum X.B.I X.B.g Finset.univ _ fun l _ =>
          Z_smul X.B.I X.B.g (hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))) (X.bw_dual l m)
        obtain ⟨t, ht, htt⟩ := this
        exact ⟨-t, neg_mem ht, by rw [htt]; ring⟩
    · rintro _ ⟨w, hw, rfl⟩
      show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w))
      refine ⟨hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ w) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) w, ?_, ?_⟩
      · exact sub_mem (hA_int X.B.I (hbwd i) (K_mv X.B.I hx hw)) (sum_mem fun l _ =>
          mul_mem (hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))) (hA_int X.B.I (hbwd l) hw))
      · simp only [Matrix.mulVec_smul, hA_smul_right, mul_sub, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
  ext i j
  have hxy : X.B.I.fmat (x * y) *ᵥ X.bw j = X.B.I.fmat x *ᵥ (X.B.I.fmat y *ᵥ X.bw j) := by
    rw [fmat_mul, Matrix.mulVec_mulVec]
  have hZ := key i (hyb j)
  simp only [PhiSub, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hZ
  rw [← hxy] at hZ

  have hI1 : hA X.B.I (X.bwd i) (X.B.I.fmat (x * y) *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E :=
    hA_int X.B.I (hbwd i) (K_mv X.B.I (K_mul X.B.I hx hy) (hbw j))
  have hI2 : ∀ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) ∈ IntAf X.B.I.F X.B.I.E :=
    fun l => hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))
  have hI3 : ∀ l, hA X.B.I (X.bwd l) (X.B.I.fmat y *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E :=
    fun l => hA_int X.B.I (hbwd l) (K_mv X.B.I hy (hbw j))
  have hIs : ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.B.I.fmat y *ᵥ X.bw j) ∈
      IntAf X.B.I.F X.B.I.E := sum_mem fun l _ => mul_mem (hI2 l) (hI3 l)
  have hD := res_eq_zero_of_Z TR v (sub_mem hI1 hIs) hZ
  simp only [leviM, Matrix.mul_apply]
  rw [resT_of_mem TR v hI1]
  simp only [resT_of_mem TR v (hI2 _), resT_of_mem TR v (hI3 _)]
  have e3 : (⟨hA X.B.I (X.bwd i) (X.B.I.fmat (x * y) *ᵥ X.bw j), hI1⟩ : IntAf X.B.I.F X.B.I.E) =
      ⟨_, sub_mem hI1 hIs⟩ + ∑ l, (⟨_, hI2 l⟩ : IntAf X.B.I.F X.B.I.E) * ⟨_, hI3 l⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_add, AddSubmonoidClass.coe_finsetSum, Subring.coe_mul]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e3, map_add (f := _), hD, zero_add, map_sum]
  simp only [map_mul]

end LeviMul

end PI.UnitaryDimensionFormula.NormCutK
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.ReferenceReprMemLattice
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting PI.UnitaryDimensionFormula.unitaryCongruence Matrix

namespace PI.UnitaryDimensionFormula.NormCutK

section Dual

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def repr0 (v : VA X.B.I) : VA X.B.I :=
  (∑ a, hA X.B.I (X.f0 a) v • X.e0 a) + (∑ a, hA X.B.I (X.e0 a) v • X.f0 a) - hA X.B.I X.z0 v • X.z0 +
    (∑ l, hA X.B.I (X.bwd l) v • X.bw l) + (∑ l, hA X.B.I (X.bw l) v • X.bwd l)

theorem Z_smul_mL {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} {u : VA X.B.I} (hc : ZMod' X.B.I X.B.g c)
    (hu : u ∈ X.B.I.Lf) : c • u ∈ mL X.B.I X.B.g := by
  obtain ⟨t, ht, rfl⟩ := hc
  rw [mul_comm, mul_smul]
  exact Submodule.smul_mem (mL X.B.I X.B.g) (⟨t, ht⟩ : IntAf X.B.I.F X.B.I.E) (smul_mem_mL X.B.I hu)

theorem reference_repr_add (v w : VA X.B.I) : repr0 X (v + w) = repr0 X v + repr0 X w := by
  simp only [repr0, hA_add_right, add_smul, Finset.sum_add_distrib]
  abel

theorem reference_repr_smul (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (v : VA X.B.I) : repr0 X (c • v) = c • repr0 X v := by
  simp only [repr0, hA_smul_right, mul_smul, ← Finset.smul_sum, smul_add, smul_sub]

theorem frame_Lf : (∀ a, X.e0 a ∈ X.B.I.Lf) ∧ (∀ a, X.f0 a ∈ X.B.I.Lf) ∧ X.z0 ∈ X.B.I.Lf ∧
    (∀ l, X.bw l ∈ X.B.I.Lf) ∧ (∀ l, X.bwd l ∈ X.B.I.Lf) := ⟨fun a => (X.vectorsInLattice.1 a).1, fun a => (X.vectorsInLattice.1 a).2, X.vectorsInLattice.2.1,
    fun l => (X.vectorsInLattice.2.2 l).1, fun l => (X.vectorsInLattice.2.2 l).2⟩

theorem reference_repr_mem_lattice {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) : repr0 X v ∈ X.B.I.Lf := by
  obtain ⟨he, hf, hz, hb, hbd⟩ := frame_Lf X
  have sm : ∀ {u w : VA X.B.I}, u ∈ X.B.I.Lf → w ∈ X.B.I.Lf → hA X.B.I u v • w ∈ X.B.I.Lf :=
    fun {u w} hu hw =>
      (Submodule.smul_mem X.B.I.Lf (⟨hA X.B.I u v, hA_int X.B.I hu hv⟩ : IntAf X.B.I.F X.B.I.E) hw : _)
  unfold repr0
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact Submodule.sum_mem _ fun a _ => sm (hf a) (he a)
  · exact Submodule.sum_mem _ fun a _ => sm (he a) (hf a)
  · exact sm hz hz
  · exact Submodule.sum_mem _ fun l _ => sm (hbd l) (hb l)
  · exact Submodule.sum_mem _ fun l _ => sm (hb l) (hbd l)

def ReprSub : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) where
  carrier := {v | v - repr0 X v ∈ mL X.B.I X.B.g}
  add_mem' {v w} hv hw := by
    show v + w - repr0 X (v + w) ∈ mL X.B.I X.B.g
    rw [reference_repr_add, show v + w - (repr0 X v + repr0 X w) = (v - repr0 X v) + (w - repr0 X w) by abel]
    exact add_mem hv hw
  zero_mem' := by
    show (0 : VA X.B.I) - repr0 X 0 ∈ mL X.B.I X.B.g
    have : repr0 X 0 = 0 := by simpa using reference_repr_smul X 0 0
    rw [this, sub_zero]; exact zero_mem _
  smul_mem' c v hv := by
    show (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v - repr0 X ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v) ∈ mL X.B.I X.B.g
    rw [reference_repr_smul, ← smul_sub]
    exact Submodule.smul_mem _ c hv

theorem T_gen (s : VA X.B.I) (tA tB : Fin D.R.rS → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (tC : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (tP tQ : Fin D.R.k → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (hs : s = (∑ a, tA a • X.e0 a) + (∑ a, tB a • X.f0 a) - tC • X.z0 + (∑ l, tP l • X.bw l) +
      (∑ l, tQ l • X.bwd l))
    (h1 : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) s - tA a))
    (h2 : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) s - tB a))
    (h3 : ZMod' X.B.I X.B.g (hA X.B.I X.z0 s - tC))
    (h4 : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd l) s - tP l))
    (h5 : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bw l) s - tQ l)) :
    s ∈ ReprSub X := by
  have neg : ∀ {x y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}, ZMod' X.B.I X.B.g (x - y) →
      ZMod' X.B.I X.B.g (y - x) := fun {x y} h => by
    have := Z_sub X.B.I X.B.g (Z_zero X.B.I X.B.g) h
    rwa [zero_sub, neg_sub] at this
  obtain ⟨he, hf, hz, hb, hbd⟩ := frame_Lf X
  have key : ∀ t : VA X.B.I, t = (∑ a, tA a • X.e0 a) + (∑ a, tB a • X.f0 a) - tC • X.z0 +
      (∑ l, tP l • X.bw l) + (∑ l, tQ l • X.bwd l) →
      t - repr0 X s = (∑ a, (tA a - hA X.B.I (X.f0 a) s) • X.e0 a) +
        (∑ a, (tB a - hA X.B.I (X.e0 a) s) • X.f0 a) - (tC - hA X.B.I X.z0 s) • X.z0 +
        (∑ l, (tP l - hA X.B.I (X.bwd l) s) • X.bw l) + (∑ l, (tQ l - hA X.B.I (X.bw l) s) • X.bwd l) := by
    intro t ht
    rw [ht, repr0]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  show s - repr0 X s ∈ mL X.B.I X.B.g
  rw [key s hs]
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact Submodule.sum_mem _ fun a _ => Z_smul_mL X (neg (h1 a)) (he a)
  · exact Submodule.sum_mem _ fun a _ => Z_smul_mL X (neg (h2 a)) (hf a)
  · exact Z_smul_mL X (neg h3) hz
  · exact Submodule.sum_mem _ fun l _ => Z_smul_mL X (neg (h4 l)) (hb l)
  · exact Submodule.sum_mem _ fun l _ => Z_smul_mL X (neg (h5 l)) (hbd l)

theorem Z_of_sym {u w : VA X.B.I} {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (h : ZMod' X.B.I X.B.g (hA X.B.I w u - sigA X.B.I c)) : ZMod' X.B.I X.B.g (hA X.B.I u w - c) := by
  have e : hA X.B.I u w - c = sigA X.B.I (hA X.B.I w u - sigA X.B.I c) := by
    rw [map_sub, sigA_sigA, hA_symm X.B.I w u]
  rw [e]
  exact Z_sig X.B.I X.B.g h

theorem hA_bw_bw (l m : Fin D.R.k) : hA X.B.I (X.bw l) (X.bw m) = 0 := by
  rw [X.bw_w l, X.bw_w m, hA_smul_left, hA_smul_right, ← mul_assoc, mul_comm (sigA X.B.I X.ew) X.ew,
    X.ew_orth, zero_mul]

theorem hA_bwd_bwd (l m : Fin D.R.k) : hA X.B.I (X.bwd l) (X.bwd m) = 0 := by
  rw [X.bwd_w l, X.bwd_w m, hA_smul_left, hA_smul_right, sigA_sigA, ← mul_assoc, X.ew_orth, zero_mul]

theorem dual_coords {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) : v - repr0 X v ∈ mL X.B.I X.B.g := by
  have sym : ∀ {u w : VA X.B.I}, ZMod' X.B.I X.B.g (hA X.B.I w u) → ZMod' X.B.I X.B.g (hA X.B.I u w) :=
    fun {u w} h => by
      have := Z_of_sym X (u := u) (w := w) (c := 0) (by rwa [map_zero, sub_zero])
      rwa [sub_zero] at this
  have mem_e : ∀ b, X.e0 b ∈ ReprSub X := fun b => by
    refine T_gen X (X.e0 b) (fun a => if a = b then 1 else 0) 0 0 0 0 ?_ ?_ ?_ ?_ ?_ ?_
    · simp [ite_smul]
    · intro a
      by_cases hab : a = b
      · subst hab
        rw [ite_eq_left rfl]
        exact Z_of_sym X (by rw [map_one]; simpa using (X.gramIntegral a a).2.2)
      · rw [ite_eq_right hab, sub_zero]
        exact sym (by simpa [Ne.symm hab] using (X.gramIntegral b a).2.2)
    · intro a; simpa using (X.gramIntegral a b).1
    · simpa using sym (X.formsAtZero.2 b).1
    · intro l; simpa using sym ((X.weightVectorsIntegral l).2.2 b).2.2.1
    · intro l; simpa using sym ((X.weightVectorsIntegral l).2.2 b).1
  have mem_f : ∀ b, X.f0 b ∈ ReprSub X := fun b => by
    refine T_gen X (X.f0 b) 0 (fun a => if a = b then 1 else 0) 0 0 0 ?_ ?_ ?_ ?_ ?_ ?_
    · simp [ite_smul]
    · intro a; simpa using (X.gramIntegral a b).2.1
    · intro a; exact (X.gramIntegral a b).2.2
    · simpa using sym (X.formsAtZero.2 b).2
    · intro l; simpa using sym ((X.weightVectorsIntegral l).2.2 b).2.2.2
    · intro l; simpa using sym ((X.weightVectorsIntegral l).2.2 b).2.1
  have zeta_mem_function_algebra : X.z0 ∈ ReprSub X := by
    refine T_gen X X.z0 0 0 (-1) 0 0 ?_ ?_ ?_ ?_ ?_ ?_
    · simp
    · intro a; simpa using (X.formsAtZero.2 a).2
    · intro a; simpa using (X.formsAtZero.2 a).1
    · rw [sub_neg_eq_add]; exact X.formsAtZero.1
    · intro l; simpa using sym (X.weightVectorsIntegral l).2.1
    · intro l; simpa using sym (X.weightVectorsIntegral l).1
  have mem_bw : ∀ m, X.bw m ∈ ReprSub X := fun m => by
    refine T_gen X (X.bw m) 0 0 0 (fun l => if l = m then X.ew else 0) 0 ?_ ?_ ?_ ?_ ?_ ?_
    · simpa [ite_smul] using X.bw_w m
    · intro a; simpa using ((X.weightVectorsIntegral m).2.2 a).2.1
    · intro a; simpa using ((X.weightVectorsIntegral m).2.2 a).1
    · simpa using (X.weightVectorsIntegral m).1
    · intro l; exact X.bw_dual l m
    · intro l; rw [hA_bw_bw X l m]; simpa using Z_zero X.B.I X.B.g
  have mem_bwd : ∀ m, X.bwd m ∈ ReprSub X := fun m => by
    refine T_gen X (X.bwd m) 0 0 0 0 (fun l => if l = m then sigA X.B.I X.ew else 0) ?_ ?_ ?_ ?_ ?_ ?_
    · simpa [ite_smul] using X.bwd_w m
    · intro a; simpa using ((X.weightVectorsIntegral m).2.2 a).2.2.2
    · intro a; simpa using ((X.weightVectorsIntegral m).2.2 a).2.2.1
    · simpa using (X.weightVectorsIntegral m).2.1
    · intro l; rw [hA_bwd_bwd X l m]; simpa using Z_zero X.B.I X.B.g
    · intro l
      refine Z_of_sym X ?_
      by_cases hlm : l = m
      · subst hlm
        rw [ite_eq_left rfl, sigA_sigA]
        simpa using X.bw_dual l l
      · rw [ite_eq_right hlm, map_zero]
        simpa [Ne.symm hlm] using X.bw_dual m l
  have hmL : mL X.B.I X.B.g ≤ ReprSub X := by
    unfold mL
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    show _ - repr0 X _ ∈ mL X.B.I X.B.g
    rw [reference_repr_smul, ← smul_sub]
    exact smul_mem_mL X.B.I (sub_mem hx (reference_repr_mem_lattice X hx))
  have hS : (Set.range X.e0 ∪ Set.range X.f0 ∪ {X.z0} ∪ Set.range X.bw ∪ Set.range X.bwd) ⊆
      (ReprSub X : Set (VA X.B.I)) := by
    rintro _ ((((⟨b, rfl⟩ | ⟨b, rfl⟩) | rfl) | ⟨m, rfl⟩) | ⟨m, rfl⟩)
    exacts [mem_e b, mem_f b, zeta_mem_function_algebra, mem_bw m, mem_bwd m]
  have hv' : v ∈ Submodule.span (IntAf X.B.I.F X.B.I.E)
      (Set.range X.e0 ∪ Set.range X.f0 ∪ {X.z0} ∪ Set.range X.bw ∪ Set.range X.bwd) ⊔
        mL X.B.I X.B.g := X.latticeSpan v hv
  exact (sup_le (Submodule.span_le.2 hS) hmL) hv'

end Dual

end PI.UnitaryDimensionFormula.NormCutK
end
end

