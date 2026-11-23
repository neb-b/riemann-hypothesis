module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KeyPow.Test

theorem fn_point_ext (V : (Sp ℂ).Opens) (f g : Γ(Sp ℂ, V))
    (h : ⊤ ≤ V → valAt' (𝟙 (Sp ℂ)) V f = valAt' (𝟙 (Sp ℂ)) V g) : f = g := by
  by_cases hV : ⊤ ≤ V
  · exact (TorusAlg.valAt'_id_bijective V (top_unique hV)).1.1 (h hV)
  · have : V = ⊥ := eq_bot_iff.2 fun x hx => hV fun y _ => by
      rwa [show y = x from Subsingleton.elim (α := PrimeSpectrum ℂ) _ _]
    subst this
    exact Subsingleton.elim _ _

theorem exists_isRig {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) :
    ∃ rig : LB.Gen (L.pull (eSec A)), rig.IsGen ∧ u.IsRig rig := by
  classical
  have h0 : (u.ex 0).left = eSec A := by
    rw [(u.ker 0).2 u.Λ.zero_mem]
    change (toUnit _ ≫ η[A]).left = η[A].left
    rw [toUnit_unit, Category.id_comp]
  have hm : ∀ j : (L.pull (eSec A)).ι, ⊤ ≤ (L.pull (eSec A)).U j → ⊤ ≤ (u.ex 0).left ⁻¹ᵁ L.U (j PUnit.unit) :=
    fun j hj y hy => by rw [h0]; exact Set.mem_iInter.1 (hj hy) PUnit.unit
  let c : (L.pull (eSec A)).ι → ℂˣ := fun j =>
    if hj : ⊤ ≤ (L.pull (eSec A)).U j then Units.mk0 _ (u.fr_ne _ 0 (hm j hj)) else 1
  let k : ∀ U : (Sp ℂ).Opens, ℂ →+* Γ(Sp ℂ, U) := fun U =>
    ((𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ).appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hk : ∀ (j) (hj : ⊤ ≤ (L.pull (eSec A)).U j),
      valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U j) (k _ (c j)) = u.fr (j PUnit.unit) 0 := fun j hj => by
    refine (valAt'_constFn (𝟙 _) (𝟙 _) (Category.id_comp _) ((L.pull (eSec A)).U j) (c j) (fun y hy => hj hy)).trans ?_
    simp only [c, dif_pos hj, Units.val_mk0]
  refine ⟨⟨fun j => Units.map (k ((L.pull (eSec A)).U j)).toMonoidHom (c j)⟩, fun i j => Units.ext (fn_point_ext _ _ _ fun hV => ?_),
    fun j hj => (hk j hj).symm⟩
  have hi : ⊤ ≤ (L.pull (eSec A)).U i := hV.trans inf_le_left
  have hj : ⊤ ≤ (L.pull (eSec A)).U j := hV.trans inf_le_right
  rw [Units.val_mul, valAt'_mul]
  have hV' : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ ((L.pull (eSec A)).U i ⊓ (L.pull (eSec A)).U j) := fun y hy => hV hy
  refine ((valAt'_res (𝟙 _) inf_le_left _ hV').trans (hk i hi)).trans (Eq.trans ?_ (congrArg _
    ((valAt'_res (𝟙 _) inf_le_right _ hV').trans (hk j hj)).symm))
  rw [u.fr_compat _ (j PUnit.unit) 0 ((top_le_preimage_inf _ _ _).2 ⟨hm i hi, hm j hj⟩)]
  congr 1
  have gg : (L.pull (eSec A)).g i j = res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => eSec A) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => eSec A) j PUnit.unit)))
      (pullU (eSec A) _ (L.g (i PUnit.unit) (j PUnit.unit))) :=
    (Fintype.prod_unique (fun k : PUnit => (res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => eSec A) i k))
      (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => eSec A) j k)))
      (pullU (eSec A) _ (L.g (i k) (j k)))) ^ (1 : ℤ))).trans (zpow_one _)
  rw [gg]
  refine Eq.symm ((valAt'_map (𝟙 _) _ _ hV').trans ((valAt'_comp (𝟙 _) (eSec A) (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))
    (L.g (i PUnit.unit) (j PUnit.unit)).val).trans ?_))
  rw [h0]
  rfl

theorem isLieBasis_of_isDiff (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g)
    (h₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v) (h₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) {c : ℂ} (hc : c ≠ 0)
    (v : Fin P.g → (epsR ℂ ⟶ P.A)) (ht : ∀ i, IsTangent (v i)) (hd : ∀ i, u.IsDiff (Pi.single i c) (v i)) :
    IsLieBasis v := by
  have := P.isAb.comm
  obtain ⟨e₁, e₂, -⟩ := LieComb.lieComb_algebra ℂ P.A P.g v ht
  have key : ∀ (d : Fin P.g → ℂ) w, IsLieComb d v w → u.IsDiff (c • d) w := fun d w h => by
    have := isDiff_sum_smul_of_isLieComb P.A P.isAb P.L _ _ u v (fun i => Pi.single i c) d w ht hd h
    convert this using 1
    funext k
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  refine ⟨ht, fun w hw => ?_⟩
  obtain ⟨z, hz, hu⟩ := h₁ w hw
  obtain ⟨w', hw', -⟩ := e₁ (c⁻¹ • z)
  have e := key _ _ hw'
  rw [smul_inv_smul₀ hc] at e
  obtain rfl : w' = w := (h₂ z).unique ⟨e₂ _ _ hw', e⟩ ⟨hw, hz⟩
  refine ⟨_, hw', fun d h => ?_⟩
  rw [← hu _ (key d _ h), inv_smul_smul₀ hc]



end GlobalTheory.KeyPow.Test
