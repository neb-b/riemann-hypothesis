module

public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueIdempotentConjAtLevelPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

namespace GlobalTheory.SeeConjIdem

theorem natCast_cpt_lt {D : D7} (g : ℕ) (PP : Pl D.host.E) (hg : (g : 𝓞 D.host.E) ∈ PP.asIdeal) :
    Valued.v (GlobalTheory.StdFrames.cpt PP (g : EAf D)) < 1 := by
  have h0 : resS D.host.F PP ((g : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D) = 0 := by
    refine (map_natCast (resS D.host.F PP) g).trans ?_
    refine (map_natCast (Ideal.Quotient.mk PP.asIdeal) g).symm.trans ?_
    exact (Ideal.Quotient.eq_zero_iff_mem).2 hg
  have h1 := (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP _).1 h0
  have e : (((g : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D) : EAf D) = (g : EAf D) := map_natCast (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D).subtype g
  rwa [e] at h1

theorem mulVec_add_apply {n : ℕ} {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) (i : Fin n) :
    (M *ᵥ (x + y)) i = (M *ᵥ x) i + (M *ᵥ y) i := by
  rw [Matrix.mulVec_add, Pi.add_apply]

theorem mulVec_smul_apply {n : ℕ} {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (c : R) (y : Fin n → R) (i : Fin n) :
    (M *ᵥ (c • y)) i = c * (M *ᵥ y) i := by
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]

theorem mulVec_zero_apply {n : ℕ} {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    (M *ᵥ (0 : Fin n → R)) i = 0 := by
  rw [Matrix.mulVec_zero, Pi.zero_apply]

theorem coord_mL {D : D7} (g : ℕ) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (hβ : GlobalTheory.PlaceModel.latFrame (Yc D 0) = GlobalTheory.NormSum.AdLattice.lat β) (w : VA (II D)) (hw : w ∈ mL (II D) g) :
    ∀ i, ∃ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D, ((β⁻¹).val *ᵥ (w : Fin (Yc D 0).rank → EAf D)) i = (g : EAf D) * a := by
  have hL : ∀ x : VA (II D), x ∈ (II D).Lf → ∀ i, ((β⁻¹).val *ᵥ (x : Fin (Yc D 0).rank → EAf D)) i ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D := by
    intro x hx
    have h1 : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.PlaceModel.latFrame (Yc D 0)) := (GlobalTheory.ConjPlaceRed.mem_Lf D x).2 hx
    rw [hβ] at h1
    exact (GlobalTheory.AdIsom.mem_hat_lat β x).1 h1
  unfold mL at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    intro i
    refine ⟨((β⁻¹).val *ᵥ (y : Fin (Yc D 0).rank → EAf D)) i, hL y hy i, ?_⟩
    have e1 : (((g : IntAf (II D).F (II D).E) : (II D).E ⊗[(II D).F] Af (II D).F)) = (g : EAf D) :=
      map_natCast (IntAf (II D).F (II D).E).subtype g
    have e2 := mulVec_smul_apply (β⁻¹).val (show EAf D from ((g : IntAf (II D).F (II D).E) : (II D).E ⊗[(II D).F] Af (II D).F)) (y : Fin (Yc D 0).rank → EAf D) i
    rw [e1] at e2
    exact e2
  | zero => intro i; exact ⟨0, zero_mem _, (mulVec_zero_apply (β⁻¹).val i).trans (mul_zero _).symm⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨a, ha, ea⟩ := hx i
    obtain ⟨b, hb, eb⟩ := hy i
    refine ⟨a + b, add_mem ha hb, ?_⟩
    refine (mulVec_add_apply (β⁻¹).val (x : Fin (Yc D 0).rank → EAf D) y i).trans ?_
    rw [ea, eb, mul_add]
  | smul c x _ hx =>
    intro i
    obtain ⟨a, ha, ea⟩ := hx i
    refine ⟨(show EAf D from c.1) * a, mul_mem c.2 ha, ?_⟩
    refine (mulVec_smul_apply (β⁻¹).val (show EAf D from c.1) (x : Fin (Yc D 0).rank → EAf D) i).trans ?_
    rw [ea]
    ring

end GlobalTheory.SeeConjIdem

namespace GlobalTheory.SeeConjIdem

theorem rank_pos (D : D7) : 0 < (Yc D 0).rank := by
  have h := Formalism.L2.SG.InstExistsPf.rank_eq D
  have h2 : (Yc D 0).rank = D.R.r := h
  obtain ⟨j, hj⟩ := D.R.m_even
  have := D.R.two_le_m
  rw [h2]
  simp only [Formalism.BasicNotions.Ranks.r]
  omega

theorem cpt_lt_of_smul_mem {D : D7} (g : ℕ) (PP : Pl D.host.E) (hg : (g : 𝓞 D.host.E) ∈ PP.asIdeal)
    (c : (II D).E ⊗[(II D).F] Af (II D).F) (hy : ∀ y ∈ (II D).Lf, c • y ∈ mL (II D) g) :
    Valued.v (GlobalTheory.StdFrames.cpt PP (show EAf D from c)) < 1 := by
  obtain ⟨β, hβ⟩ := GlobalTheory.AdIsom.exists_eq_lat (GlobalTheory.AdIsom.selfDual_isFullLattice
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame (Yc D 0)))
  let i0 : Fin (Yc D 0).rank := ⟨0, rank_pos D⟩
  let y : Fin (Yc D 0).rank → EAf D := β.val *ᵥ Pi.single i0 1
  have hby : (β⁻¹).val *ᵥ y = Pi.single i0 1 := by
    simp only [y, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let yv : VA (II D) := y
  have hyL : yv ∈ (II D).Lf := by
    refine (GlobalTheory.ConjPlaceRed.mem_Lf D y).1 ?_
    rw [hβ]
    refine (GlobalTheory.AdIsom.mem_hat_lat β y).2 fun i => ?_
    rw [hby, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨a, ha, ea⟩ := coord_mL g β hβ _ (hy yv hyL) i0
  have e3 : ((β⁻¹).val *ᵥ ((c • yv : VA (II D)) : Fin (Yc D 0).rank → EAf D)) i0 = (show EAf D from c) := by
    refine (mulVec_smul_apply (β⁻¹).val (show EAf D from c) y i0).trans ?_
    rw [hby, Pi.single_eq_same, mul_one]
  have ea' : (show EAf D from c) = (g : EAf D) * a := e3.symm.trans ea
  rw [ea', map_mul, Valuation.map_mul, mul_comm]
  exact mul_lt_one_of_nonneg_of_lt_one_right ((GlobalTheory.AdIsom.mem_OA a).1 ha PP) zero_le (natCast_cpt_lt g PP hg)

theorem resS_of_idem {D : D7} (PP : Pl D.host.E) (e s : EAf D) (he : e * e = e) (hs : s * s = s) (hes : e * s = 0)
    (hei : e ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D) (hsi : s ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D)
    (key : Valued.v (GlobalTheory.StdFrames.cpt PP (1 - e - s)) < 1) :
    (GlobalTheory.StdFrames.cpt PP e = 1 → resS D.host.F PP ⟨e, hei⟩ = 1 ∧ resS D.host.F PP ⟨s, hsi⟩ = 0) ∧
      (GlobalTheory.StdFrames.cpt PP e ≠ 1 → resS D.host.F PP ⟨e, hei⟩ = 0 ∧ resS D.host.F PP ⟨s, hsi⟩ = 1) := by
  have he' : GlobalTheory.StdFrames.cpt PP e * GlobalTheory.StdFrames.cpt PP e = GlobalTheory.StdFrames.cpt PP e := by
    rw [← map_mul, he]
  have hs' : GlobalTheory.StdFrames.cpt PP s * GlobalTheory.StdFrames.cpt PP s = GlobalTheory.StdFrames.cpt PP s := by
    rw [← map_mul, hs]
  have hes' : GlobalTheory.StdFrames.cpt PP e * GlobalTheory.StdFrames.cpt PP s = 0 := by
    rw [← map_mul, hes, map_zero]
  have i01 : ∀ x : PP.adicCompletion D.host.E, x * x = x → x = 0 ∨ x = 1 := by
    intro x hx
    have : x * (x - 1) = 0 := by rw [mul_sub, hx, mul_one, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have r0 : ∀ t : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D, GlobalTheory.StdFrames.cpt PP (t : EAf D) = 0 → resS D.host.F PP t = 0 :=
    fun t h => (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP t).2 (by rw [h, map_zero]; exact zero_lt_one)
  have r1 : ∀ t : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D, GlobalTheory.StdFrames.cpt PP (t : EAf D) = 1 → resS D.host.F PP t = 1 := by
    intro t h
    have := r0 (1 - t) (by
      rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one, map_sub, map_one, h, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  constructor
  · intro h1
    have hf0 : GlobalTheory.StdFrames.cpt PP s = 0 := by
      rw [h1, one_mul] at hes'; exact hes'
    exact ⟨r1 ⟨e, hei⟩ h1, r0 ⟨s, hsi⟩ hf0⟩
  · intro hne
    have he0 : GlobalTheory.StdFrames.cpt PP e = 0 := (i01 _ he').resolve_right hne
    have hf1 : GlobalTheory.StdFrames.cpt PP s = 1 := by
      rcases i01 _ hs' with h | h
      · exfalso
        have h1 : GlobalTheory.StdFrames.cpt PP (1 - e - s) = 1 := by
          rw [map_sub (GlobalTheory.StdFrames.cpt PP), map_sub (GlobalTheory.StdFrames.cpt PP), map_one, he0, h, sub_zero, sub_zero]
        rw [h1, Valuation.map_one] at key
        exact lt_irrefl _ key
      · exact h
    exact ⟨r0 ⟨e, hei⟩ he0, r1 ⟨s, hsi⟩ hf1⟩

theorem resS_idem_conj : ∀ {D : D7} (g : ℕ) (ew : (II D).E ⊗[(II D).F] Af (II D).F), ew * ew = ew → ew * sigA (II D) ew = 0 → ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → (∀ y ∈ (II D).Lf, (1 - ew - sigA (II D) ew) • y ∈ mL (II D) g) → ∀ PP : Pl D.host.E, ((g : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ (h1 : ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (h2 : sigA (II D) ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (GlobalTheory.StdFrames.cpt PP ew = 1 → resS D.host.F PP ⟨ew, h1⟩ = 1 ∧ resS D.host.F PP ⟨sigA (II D) ew, h2⟩ = 0) ∧ (GlobalTheory.StdFrames.cpt PP ew ≠ 1 → resS D.host.F PP ⟨ew, h1⟩ = 0 ∧ resS D.host.F PP ⟨sigA (II D) ew, h2⟩ = 1) := by
  intro D g ew hid hperp hint hy PP hg
  have hs : sigA (II D) ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.AdIsom.cjA_mem hint
  have hss : sigA (II D) ew * sigA (II D) ew = sigA (II D) ew := by rw [← map_mul, hid]
  exact ⟨hint, hs, resS_of_idem PP ew (sigA (II D) ew) hid hss hperp hint hs (cpt_lt_of_smul_mem g PP hg _ hy)⟩

end GlobalTheory.SeeConjIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeImageAdelicUnitary
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
open scoped TensorProduct

namespace GlobalTheory.AdIsomImage

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.NormSum.AdLattice (lat)

section Ring

variable {A : Type} [CommRing A] {n : ℕ}

theorem inv_mul_mulVec (g β : GL (Fin n) A) (y : Fin n → A) :
    ((g * β)⁻¹).val *ᵥ y = (β⁻¹).val *ᵥ ((g⁻¹).val *ᵥ y) := by
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

theorem gram_mul (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (g β : GL (Fin n) A)
    (h : Formalism.UG.cT σ g.val * J * g.val = J) :
    Formalism.UG.cT σ (g * β).val * J * (g * β).val = Formalism.UG.cT σ β.val * J * β.val := by
  have hc : Formalism.UG.cT σ (g * β).val = Formalism.UG.cT σ β.val * Formalism.UG.cT σ g.val := by
    rw [Units.val_mul]
    exact GlobalTheory.StdFrames.cT_mul' σ _ _
  calc Formalism.UG.cT σ (g * β).val * J * (g * β).val
      = Formalism.UG.cT σ β.val * (Formalism.UG.cT σ g.val * J * g.val) * β.val := by
        rw [hc, Units.val_mul]
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ β.val * J * β.val := by rw [h]

end Ring

variable {D : D7}

theorem fin_cA (z : Formalism.L2.Theta.AE D) :
    ((swapAE D).comp (finPart D)) (cA D z) = cjA D (((swapAE D).comp (finPart D)) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e =>
    simp [cA, cjA, finPart, swapAE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem finE_unitary (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (cjA D) (finE V g).val * V.gram.map (inc D) * (finE V g).val = V.gram.map (inc D) := by
  have hg : Formalism.UG.cT (cA D) (g.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) * V.gram.map (incA D) *
      (g.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = V.gram.map (incA D) := g.2
  have key := congrArg ((swapAE D).comp (finPart D)).mapMatrix hg
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul] at key
  have hcT : ∀ M : Matrix (Fin V.rank) (Fin V.rank) (AE D),
      (Formalism.UG.cT (cA D) M).map ((swapAE D).comp (finPart D)) =
        Formalism.UG.cT (cjA D) (M.map ((swapAE D).comp (finPart D))) := by
    intro M
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply]
    exact fin_cA (M j i)
  have hJ : (V.gram.map (incA D)).map ((swapAE D).comp (finPart D)) = V.gram.map (inc D) := by
    rw [Matrix.map_map]
    congr 1
  have hfin : ((finE V g).val : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) =
      (g.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map ((swapAE D).comp (finPart D)) := rfl
  rw [hcT, hJ] at key
  rw [hfin]
  exact key

theorem carries_iff {n : ℕ} (g : GL (Fin n) (EAf D)) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    Formalism.L2.Herm.Carries g Λ Λ' ↔ ∀ y, y ∈ hat Λ' ↔ (g⁻¹).val *ᵥ y ∈ hat (D := D) Λ := by
  unfold Formalism.L2.Herm.Carries
  exact forall_congr' fun y => Iff.rfl

theorem imageSt (D : D7) : ImageSt D := by
  intro V Λ hΛ d _hd
  obtain ⟨β, rfl, hβ⟩ := exists_orth hΛ
  have hcar : Formalism.L2.Herm.Carries (finE V d) (lat β) (lat (finE V d * β)) := by
    rw [carries_iff]
    intro y
    rw [mem_hat_lat, mem_hat_lat, inv_mul_mulVec]
  have hgram : GlobalTheory.StdFrames.gramOf V (finE V d * β) = 1 :=
    (gram_mul (cjA D) (V.gram.map (inc D)) (finE V d) β (finE_unitary V d)).trans hβ
  have hlat := GlobalTheory.NormSum.AdLattice.lat_isLattice (finE V d * β)
  refine ⟨⟨lat (finE V d * β), hlat.toIsLattice, hcar⟩, fun Λ' hΛ' hc => ?_⟩
  have hhat : hat (D := D) Λ' = hat (lat (finE V d * β)) := by
    ext y
    exact ((carries_iff _ _ _).1 hc y).trans (((carries_iff _ _ _).1 hcar y).symm)
  have heq : Λ' = lat (finE V d * β) := by
    ext x
    rw [← inc_mem_hat_iff hlat x, ← hhat]
    exact ⟨inc_mem_hat, GlobalTheory.GlueUnique.mem_of_inc_mem_hat hΛ'.fg⟩
  rw [heq]
  exact isSelfDualC_lat (by rw [hgram]; exact unimod_one)

end GlobalTheory.AdIsomImage

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFrameIntegralityConditions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjRead.DetUnit

open Classical

section Val
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

theorem v_sign_smul {n : ℕ} (s : Equiv.Perm (Fin n)) (x : K) : v (Equiv.Perm.sign s • x) = v x := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
  · rw [h, one_smul]
  · rw [h, Units.neg_smul, one_smul, Valuation.map_neg]

theorem v_det_le {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : ∀ i j, v (M i j) ≤ 1) : v M.det ≤ 1 := by
  rw [Matrix.det_apply]
  refine Valuation.map_sum_le v fun s _ => ?_
  rw [v_sign_smul, map_prod]
  exact Finset.prod_le_one' fun i _ => h _ _

theorem v_det_eq_one {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (d : Fin n → K) (hd : ∀ a, v (d a) = 1)
    (h : ∀ a b, v (M a b - if a = b then d a else 0) < 1) : v M.det = 1 := by
  have hle : ∀ i j, v (M i j) ≤ 1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have h1 := h i i
      rw [if_pos rfl] at h1
      have : M i i = (M i i - d i) + d i := by ring
      rw [this]
      exact (Valuation.map_add v _ _).trans (max_le h1.le (hd i).le)
    · have h1 := h i j
      rw [if_neg hij, sub_zero] at h1
      exact h1.le
  have hdiag : ∀ i, v (M i i) = 1 := by
    intro i
    have h1 := h i i
    rw [if_pos rfl] at h1
    have : M i i = (M i i - d i) + d i := by ring
    rw [this, Valuation.map_add_eq_of_lt_right v (by rw [hd i]; exact h1), hd i]
  rw [Matrix.det_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))]
  have hmain : v (Equiv.Perm.sign (1 : Equiv.Perm (Fin n)) • ∏ i, M ((1 : Equiv.Perm (Fin n)) i) i) = 1 := by
    rw [v_sign_smul, map_prod]
    exact Finset.prod_eq_one fun i _ => hdiag i
  have hrest : v (∑ s ∈ Finset.univ.erase (1 : Equiv.Perm (Fin n)), Equiv.Perm.sign s • ∏ i, M (s i) i) < 1 := by
    refine Valuation.map_sum_lt v one_ne_zero fun s hs => ?_
    have hs1 : s ≠ 1 := Finset.ne_of_mem_erase hs
    obtain ⟨i, hi⟩ : ∃ i, s i ≠ i := by
      by_contra hc
      push_neg at hc
      exact hs1 (Equiv.ext hc)
    rw [v_sign_smul, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    have h1 := h (s i) i
    rw [if_neg hi, sub_zero] at h1
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (Finset.prod_le_one' fun j _ => hle _ _)) h1
  rw [Valuation.map_add_eq_of_lt_left v (by rw [hmain]; exact hrest), hmain]

end Val

end GlobalTheory.SeeConjRead.DetUnit

namespace GlobalTheory.SeeConjRead.DetUnit

theorem val_le_of_int {D : D7} (Q : Pl D.host.E) (x : EAf D) (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Valued.v (GlobalTheory.StdFrames.cpt Q x) ≤ 1 := by
  have := (GlobalTheory.StdFrames.mem_OA_iff x).1 hx Q
  rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at this

theorem val_det_le {D : D7} {n : ℕ} (Q : Pl D.host.E) (M : Matrix (Fin n) (Fin n) (EAf D))
    (hM : ∀ i j, M i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : Valued.v (GlobalTheory.StdFrames.cpt Q M.det) ≤ 1 := by
  rw [RingHom.map_det]
  exact v_det_le _ _ fun i j => val_le_of_int Q _ (hM i j)

theorem det_unit : ∀ {D : D7} {n : ℕ} (β₀ : GL (Fin n) (EAf D)) (J U W : Matrix (Fin n) (Fin n) (EAf D)) (Q : Pl D.host.E) (d : Fin n → EAf D), (∀ i j, (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, ((β₀⁻¹).val * U) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, ((β₀⁻¹).val * W) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ a, Valued.v (GlobalTheory.StdFrames.cpt Q (d a)) = 1) → (∀ a b, SmallAt Q ((Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W) a b - if a = b then d a else 0)) → Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * W).det) = 1 := by
  intro D n β₀ J U W Q d hG hA hB hd hX
  set A := (β₀⁻¹).val * U with hAdef
  set B := (β₀⁻¹).val * W with hBdef
  set G := Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val with hGdef
  have hU : U = β₀.val * A := by rw [hAdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hW : W = β₀.val * B := by rw [hBdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hX' : Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W = Formalism.UG.cT (GlobalTheory.StdFrames.sg D) A * G * B := by
    rw [hGdef, hU, hW, GlobalTheory.StdFrames.cT_mul']
    simp only [Matrix.mul_assoc]
  have h1 : Valued.v (GlobalTheory.StdFrames.cpt Q (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W).det) = 1 := by
    rw [RingHom.map_det]
    refine v_det_eq_one _ _ (fun a => GlobalTheory.StdFrames.cpt Q (d a)) hd fun a b => ?_
    have := hX a b
    unfold SmallAt at this
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    split_ifs at this ⊢ with hab
    · rwa [map_sub] at this
    · rwa [sub_zero] at this ⊢
  rw [hX', Matrix.det_mul, Matrix.det_mul] at h1
  simp only [map_mul] at h1
  have ha : Valued.v (GlobalTheory.StdFrames.cpt Q (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) A).det) ≤ 1 :=
    val_det_le Q _ fun i j => Formalism.UG.P.csDual_sig_mem _ (hA j i)
  have hg : Valued.v (GlobalTheory.StdFrames.cpt Q G.det) ≤ 1 := val_det_le Q _ hG
  have hb : Valued.v (GlobalTheory.StdFrames.cpt Q B.det) ≤ 1 := val_det_le Q _ hB
  refine le_antisymm hb ?_
  rw [← h1]
  exact mul_le_of_le_one_left' (mul_le_one' ha hg)

end GlobalTheory.SeeConjRead.DetUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentLevelMovesDualVectorUpper
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

namespace GlobalTheory.SeeConjBwd


open Formalism.L2.SG.Pf.BunEx.Unip Formalism.L2.SG.Pf.unitaryCongruence in
theorem bwd_move : ∀ (I : AutInst) (g : ℕ) {r k : ℕ} (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Af I.F), Formalism.L2.SG.Pf.BunEx.Unip.FH I g e0 f0 z0 bw bwd ew → ∀ x : I.Gf, x ∈ I.Kset → K2cong I g e0 z0 bw x → ∀ j : Fin k, (I.fmat x - 1) *ᵥ bwd j ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo I g (Set.range e0 ∪ bwd '' {l | j < l}) := by
  intro I g r k e0 f0 z0 bw bwd ew h x hx hcx j
  have hm := h.mem
  have hcx' := Formalism.L2.SG.Pf.unitaryCongruence.cong_inv I g e0 z0 bw hx hcx
  have hw : (I.fmat x - 1) *ᵥ bwd j ∈ I.Lf := K_sub_mv I hx (hm.2.2 j).2
  refine Formalism.L2.SG.Pf.BunEx.Unip.mem_Mo_of (Formalism.L2.SG.Pf.BunEx.Unip.exp h _ hw) ?_
  set w := (I.fmat x - 1) *ᵥ bwd j with hwdef
  unfold Formalism.L2.SG.Pf.BunEx.Unip.Rc
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact span_Mo (sumSpan I _ _ _ (fun a _ => hA_int I (hm.1 a).2 hw)
      (fun a _ => Or.inl ⟨a, rfl⟩))
  · refine Formalism.L2.SG.Pf.unitaryCongruence.mL_Mo I (sumZ I g _ _ _ (fun a _ => ?_) (fun a _ => (hm.1 a).2))
    rw [hwdef, Formalism.L2.SG.Pf.BunEx.Unip.adj]
    refine Zleft I g (hm.2.2 j).2 ?_ (hcx'.1 a)
    rintro _ ⟨c, -, rfl⟩
    exact ((h.W j).2.2 c).2.2.1
  · refine Formalism.L2.SG.Pf.unitaryCongruence.mL_Mo I (Zv I g ?_ hm.2.1)
    rw [hwdef, Formalism.L2.SG.Pf.BunEx.Unip.adj]
    refine Zleft I g (hm.2.2 j).2 ?_ hcx'.2.1
    rintro _ ⟨c, rfl⟩
    exact ((h.W j).2.2 c).2.2.1
  · refine Formalism.L2.SG.Pf.unitaryCongruence.mL_Mo I (sumZ I g _ _ _ (fun i _ => ?_) (fun i _ => (hm.2.2 i).1))
    have e : hA I (bwd i) w = 0 := by
      rw [hwdef, Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right, bdbd h, sub_zero, h.bwd_w i,
        h.bwd_w j, Matrix.mulVec_smul]
      exact hA_sew I h.orth _ _
    rw [e]; exact Z_zero I g
  · refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hji : j < i
    · exact span_Mo (smul_span I (hA_int I (hm.2.2 i).1 hw) (Or.inr ⟨i, hji, rfl⟩))
    · refine Formalism.L2.SG.Pf.unitaryCongruence.mL_Mo I (Zv I g ?_ (hm.2.2 i).2)
      rw [hwdef, Formalism.L2.SG.Pf.BunEx.Unip.adj]
      refine Zleft I g (hm.2.2 j).2 ?_ (hcx'.2.2 i)
      rintro _ (⟨c, rfl⟩ | ⟨l, hl, rfl⟩)
      · exact ((h.W j).2.2 c).2.2.1
      · have hl' : l.1 < i.1 := hl
        have hlj : j ≠ l := fun e => hji (by rw [e]; exact hl')
        have := Zsym (h.dual j l)
        rw [if_neg hlj, map_zero, sub_zero] at this
        exact this

end GlobalTheory.SeeConjBwd
end

