module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfWave
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonvanishingFiniteDatumDefiniteLift
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AdjDatumNe

open GlobalTheory.AdelicLatMove GlobalTheory.PlaceVec

def rectOne (R : Type) [Zero R] [One R] (b a : ℕ) : Matrix (Fin b) (Fin a) R :=
  fun i j => if i.val = j.val then 1 else 0

theorem lowZero_rectOne (R : Type) [Zero R] [One R] (b a k : ℕ) : LowZero k (rectOne R b a) :=
  fun i j hi hj => if_neg (by omega)

theorem topL_rectOne (R : Type) [Zero R] [One R] {b a : ℕ} (h : a ≤ b) : topL a (rectOne R b a) = 1 := by
  ext i j
  have h1 : i.val < b ∧ j.val < a := ⟨by omega, j.2⟩
  unfold topL rectOne
  rw [dif_pos h1, Matrix.one_apply]
  simp only [Fin.ext_iff]

theorem sandwich_cancel' {R : Type} [CommRing R] {m n : ℕ} (A A' G G' : Matrix (Fin m) (Fin m) R)
    (B B' H H' : Matrix (Fin n) (Fin n) R) (N : Matrix (Fin m) (Fin n) R) (c : R) (hA : A' * A = 1) (hG : G * G' = 1)
    (hB : B' * B = 1) (hH : H * H' = 1) : (A' * G') * (c • ((G * A) * N * (B' * H'))) * (H * B) = c • N := by
  have hG' : G' * G = 1 := mul_eq_one_comm.1 hG
  have hH' : H' * H = 1 := mul_eq_one_comm.1 hH
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = (A' * (G' * G) * A) * N * (B' * (H' * H) * B) := by simp only [Matrix.mul_assoc]
    _ = N := by rw [hG', hH', Matrix.mul_one, Matrix.mul_one, hA, hB, Matrix.one_mul, Matrix.mul_one]

variable {D : D7}

theorem toEAf_surjective (z : EAf D) : ∃ w : AE D, toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul x α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] x, rfl⟩
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, by rw [RingHom.map_add (f := _), hs, ht]⟩

theorem exists_half_frMapAdj (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {e : AE D} (he : e * e = e) (I : Matrix (Fin S.rank) (Fin T.rank) (EAf D)) :
    ∃ x : WO S T, IsHalf (cA D e) x ∧ frMapAdj S T βS βT x = toEAf D e • I := by
  choose N hN using fun (i : Fin S.rank) (j : Fin T.rank) => toEAf_surjective
    (((S.gram.map (eToEAf D) * βS.val) * I * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D))) i j)
  refine ⟨Matrix.of fun j i => cA D (e * N i j), fun j i => ?_, ?_⟩
  · change cA D e * cA D (e * N i j) = cA D (e * N i j)
    rw [← RingHom.map_mul, ← mul_assoc, he]
  · rw [frMapAdj_eq, ← sandwich_cancel' _ _ _ _ _ _ _ _ I (toEAf D e) βS.inv_mul (gram_map_mul_inv S) βT.inv_mul
      (gram_map_mul_inv T)]
    congr 2
    refine Matrix.ext fun i j => ?_
    change cF D (toEAf D (cA D (e * N i j))) = toEAf D e * _
    rw [toEAf_cA, cF_cF_toEAf, RingHom.map_mul, hN]

theorem idemSum_res {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) :
    ∃ hi : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      ∀ PP ∈ P, Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D e, hi⟩ = 1 := by
  have he := idemSum_mul_self h
  have hi : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he]))
  refine ⟨hi, fun PP hPP => ?_⟩
  obtain ⟨⟨es, h1, h2⟩, -⟩ := h
  have h3 : es PP * ∑ j ∈ P, es j = es PP :=
    GlobalTheory.PlaceModelSum.mul_sum_orth (fun i hi => (h1 i hi).1) (fun i hi j hj hij =>
      (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 i hi).1 (h1 j hj).1).resolve_left fun h =>
        hij (isIdemAt_inj (h1 j hj) (h ▸ h1 i hi))) hPP
  rw [← h2] at h3
  obtain ⟨k, hk⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)
  have h4 : (⟨toEAf D (es PP), k⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D e, hi⟩ = ⟨toEAf D (es PP), k⟩ :=
    Subtype.ext (by change toEAf D (es PP) * toEAf D e = toEAf D (es PP); rw [← RingHom.map_mul, h3])
  have h5 := congrArg (Formalism.L2.DIV.resS D.host.F PP) h4
  rwa [RingHom.map_mul, hk, one_mul] at h5

theorem isIntM_smul_rectOne {ε : EAf D} (hi : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (b a : ℕ) :
    IsIntM (ε • rectOne (EAf D) b a) := by
  intro i j
  change ε * (if i.val = j.val then 1 else 0) ∈ _
  split_ifs
  · rwa [mul_one]
  · rw [mul_zero]; exact zero_mem _

theorem redM_smul_rectOne {ε : EAf D} (hi : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E)
    (h : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hi⟩ = 1) (b a : ℕ) :
    redM PP (ε • rectOne (EAf D) b a) = rectOne _ b a := by
  funext i j
  refine (dif_pos (isIntM_smul_rectOne hi b a i j)).trans ?_
  by_cases hij : i.val = j.val
  · refine Eq.trans (congrArg _ (Subtype.ext ?_)) (h.trans (if_pos hij).symm)
    change ε * (if i.val = j.val then 1 else 0) = ε
    rw [if_pos hij, mul_one]
  · refine Eq.trans (congrArg _ (Subtype.ext ?_)) ((RingHom.map_zero _).trans (if_neg hij).symm)
    change ε * (if i.val = j.val then 1 else 0) = 0
    rw [if_neg hij, mul_zero]

theorem exists_datum_ne_zero : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q P : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (e : AE D), T.rank ≤ S.rank → IsIdemSum e P → (∀ PP ∈ Pg, PP ∈ P) → (∀ PP ∈ Q, PP ∈ P) → ∃ x : WO S T, IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧ omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) * omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) ≠ 0 := by
  intro D S T βS βT Pg Q P ξ e hr he hg hQ
  obtain ⟨x, hx, hx'⟩ := exists_half_frMapAdj S T βS βT (idemSum_mul_self he) (rectOne _ _ _)
  obtain ⟨hi, hres⟩ := idemSum_res he
  refine ⟨x, hx, ?_, ?_⟩
  · rw [hx']; exact isIntM_smul_rectOne hi _ _
  · have key : ∀ PP ∈ P, LowZero T.rank (redM PP (frMapAdj S T βS βT x)) ∧
        topL T.rank (redM PP (frMapAdj S T βS βT x)) = 1 := fun PP hPP => by
      rw [hx', redM_smul_rectOne hi PP (hres PP hPP)]
      exact ⟨lowZero_rectOne _ _ _ _, topL_rectOne _ hr⟩
    refine mul_ne_zero ?_ ?_
    · unfold omegaK
      rw [if_pos fun PP hPP => key PP (hg PP hPP)]
      exact one_ne_zero
    · unfold omegaQ
      rw [dif_pos fun PP hPP => ⟨(key PP (hQ PP hPP)).1, by
        rw [(key PP (hQ PP hPP)).2, Matrix.det_one]; exact isUnit_one⟩]
      exact Finset.prod_ne_zero_iff.2 fun PP _ => zpow_ne_zero _ (Units.ne_zero _)

end GlobalTheory.AdjDatumNe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InnerSteps

variable {D : D7}

theorem hasInfQ_tauE {χ : Formalism.L2.Host.HChar D.host.E} {a : D.R.Psi → ℚ}
    (h : χ.HasInfQ (Formalism.L2.Host.embPsi D.host) a) : χ.HasInfQ (tauE D) fun τ => a (D.eTau τ) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨fun τ => n (D.eTau τ), fun τ => hn _, fun k => ?_⟩
  rw [h k]
  exact (Equiv.prod_comp D.eTau (fun g => (Formalism.L2.Host.embPsi D.host g (k : D.host.E) /
      ((‖Formalism.L2.Host.embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ)) ^ n g)).symm

theorem hasInfExp_mul_zero {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ 0) : HasInfExp D (χ * η) τ a := by
  obtain ⟨n, hn, h1, h2⟩ := hχ
  obtain ⟨m, hm, -, h3⟩ := hη
  have hm0 : m = 0 := by exact_mod_cast hm.trans (mul_zero _)
  refine ⟨n, hn, h1, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.mul_apply, Circle.coe_mul, h2 θ hθ x hx hτ, h3 θ hθ x hx hτ, hm0, zpow_zero, mul_one]

theorem exp_chrStep {T0 : Type} (L : LevCh D T0) {μ0 : T0} (hL : L.Is μ0) (t : T0) (k : Fin D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (Lift.chrStep (L.mu t) L.eta ((k : ℕ) + 1)).1 τ (expS D k τ) ∧
      HasInfExp D (Lift.chrStep (L.mu t) L.eta ((k : ℕ) + 1)).2 τ (expT D k τ) := by
  have h1 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 k) (hasInfQ_tauE (L.C.isMu0 k).inf) τ
  simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
  have h2 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
    (hasInfQ_tauE (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  haveI : IsTotallyComplex D.host.E := by infer_instance
  have h3 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun _ => 0) (hL.xi t)
    ⟨fun _ => 0, fun _ => by norm_num, fun x => by
      rw [GlobalTheory.TypeValues.inf_eq_one _ hn ho x]; simp⟩ τ
  have h4 : HasInfExp D (L.mu t ((k : ℕ) + 1)) τ (-(D.hc τ).e k) := hasInfExp_mul_zero h1 h3
  unfold Lift.chrStep
  by_cases hk : Even (k : ℕ)
  · rw [if_pos hk.add_one, (exp_of_even hk τ).1, (exp_of_even hk τ).2]
    exact ⟨hasInfExp_div h4 h2, h4⟩
  · rw [if_neg (fun h => hk (by simpa [Nat.odd_add_one, Nat.not_odd_iff_even] using h)), (exp_of_odd hk τ).1,
      (exp_of_odd hk τ).2]
    exact ⟨h4, hasInfExp_div h4 h2⟩

theorem toEAf_surjective : Function.Surjective (toEAf D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul x a => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

theorem sum_mul_idem {R ι : Type} [CommRing R] (p : ι → R) (s : Finset ι) (h : ∀ i ∈ s, p i * p i = p i)
    (h0 : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → p i * p j = 0) {i : ι} (hi : i ∈ s) : p i * (∑ i ∈ s, p i) = p i := by
  rw [Finset.mul_sum, Finset.sum_eq_single i (fun j hj hji => h0 i hi j hj hji) (fun h => absurd hi h), h i hi]

theorem resS_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) :
    ∃ hi : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP ∈ P, resS D.host.F PP ⟨toEAf D e, hi⟩ = 1 := by
  have he := GlobalTheory.PlaceDatum.idemSum_mul_self h
  have hint : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he]))
  refine ⟨hint, fun PP hP => ?_⟩
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := h
  have h1 : ∀ i ∈ P, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ P, ∀ j ∈ P, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es P h1 (hsum ▸ hc)
  have h2 : ∀ i ∈ P, ∀ j ∈ P, j ≠ i → es i * es j = 0 := fun i hi j hj hji =>
    GlobalTheory.PlaceDatum.idemAt_mul (hes i hi) (hes j hj) (hcross i hi j hj) (hcross j hj i hi) hji
  have h3 : es PP * e = es PP := by
    rw [hsum]; exact sum_mul_idem (R := AE D) es P h1 h2 hP
  obtain ⟨h4, h5⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (es PP) PP (hes PP hP)
  have h6 : (⟨_, h4⟩ * ⟨_, hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, h4⟩ :=
    Subtype.ext (by change toEAf D _ * toEAf D _ = toEAf D _; rw [← RingHom.map_mul, h3])
  have h7 := congrArg (resS D.host.F PP) h6
  rwa [map_mul, h5, one_mul] at h7

def rect (κ : Type) [Zero κ] [One κ] (b a : ℕ) : Matrix (Fin b) (Fin a) κ := fun i j => if i.val = j.val then 1 else 0

theorem lowZero_rect {κ : Type} [Zero κ] [One κ] (b a k : ℕ) : LowZero k (rect κ b a) :=
  fun i j hi hj => if_neg (by omega)

theorem topL_rect {κ : Type} [Zero κ] [One κ] {b a k : ℕ} (hb : k ≤ b) (ha : k ≤ a) : topL k (rect κ b a) = 1 := by
  ext i j
  unfold topL rect
  rw [dif_pos ⟨lt_of_lt_of_le i.2 hb, lt_of_lt_of_le j.2 ha⟩, Matrix.one_apply]
  simp only [Fin.ext_iff]

theorem frame_smul {R : Type} [CommRing R] {a b : ℕ} (p : GL (Fin a) R) (q : GL (Fin b) R) (c : R)
    (y z : Matrix (Fin b) (Fin a) R) (h : ∀ i j, z i j = c * (q.val * y * (p⁻¹).val) i j) (i : Fin b) (j : Fin a) :
    ((q⁻¹).val * z * p.val) i j = c * y i j := by
  have hz : z = c • (q.val * y * (p⁻¹).val) := Matrix.ext h
  rw [hz, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc q.val, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
    Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul]

theorem exists_rect (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D))
    {e : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) :
    ∃ x : WO S T, IsHalf e x ∧ IsIntM (frMapO S T βS βT x) ∧
      ∀ PP ∈ P, redM PP (frMapO S T βS βT x) = rect _ _ _ := by
  obtain ⟨hi, hr⟩ := resS_idemSum h
  have he := GlobalTheory.PlaceDatum.idemSum_mul_self h
  choose s hs using toEAf_surjective (D := D)
  let x : Matrix (Fin T.rank) (Fin S.rank) (AE D) :=
    fun i j => e * s (HMul.hMul (HMul.hMul βT.val (rect (Datum.EAf D) T.rank S.rank)) (βS⁻¹).val i j)
  have hf : ∀ i j, frMapO S T βS βT x i j = if i.val = j.val then toEAf D e else 0 := by
    intro i j
    refine (frame_smul βS βT (toEAf D e) (rect (Datum.EAf D) T.rank S.rank) (x.map (toEAf D)) (fun i j => ?_) i j).trans ?_
    · exact (RingHom.map_mul _ _ _).trans (congrArg _ (hs _))
    · rw [rect, mul_ite, mul_one, mul_zero]
  have hI : IsIntM (frMapO S T βS βT x) := fun i j => by
    rw [hf]
    split_ifs
    · exact hi
    · exact zero_mem _
  refine ⟨x, fun i j => by simp only [x]; rw [← mul_assoc, he], hI, fun PP hP => ?_⟩
  ext i j
  refine (dif_pos (hI i j)).trans ?_
  unfold rect
  split_ifs with hij
  · rw [← hr PP hP]
    exact congrArg _ (Subtype.ext ((hf i j).trans (if_pos hij)))
  · rw [← map_zero (resS D.host.F PP)]
    exact congrArg _ (Subtype.ext ((hf i j).trans (if_neg hij)))

theorem omegaG_ne_zero {a b : ℕ} (hab : a ≤ b) (L : LevDat D.host.E ℂ a) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hy : ∀ PP ∈ L.Pg, y PP = rect _ _ _) :
    omegaG L χ y ≠ 0 := by
  unfold omegaG
  split_ifs with h
  · refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) ?_) ?_
    · exact Finset.prod_ne_zero_iff.2 fun _ _ => Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _
    · exact Finset.prod_ne_zero_iff.2 fun _ _ => inv_ne_zero (Units.ne_zero _)
  · refine absurd ⟨fun PP hP => ?_, fun _ => 1, fun PP => ?_, fun _ => one_mem _, ?_⟩ h
    · rw [hy PP hP]; exact lowZero_rect _ _ _
    · rw [hy PP.1 PP.2, topL_rect hab le_rfl, Units.val_one]
    · convert L.P.H.one_mem using 1
      funext PP
      exact blockDiagonalExtendByOnePrimeField_one _ _

theorem omegaQ_ne_zero {a b r : ℕ} (ha : r ≤ a) (hb : r ≤ b) (Q : Finset (Pl D.host.E))
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hy : ∀ PP ∈ Q, y PP = rect _ _ _) :
    omegaQ Q r ξ k y ≠ 0 := by
  unfold omegaQ
  split_ifs with h
  · exact Finset.prod_ne_zero_iff.2 fun _ _ => zpow_ne_zero _ (Units.ne_zero _)
  · refine absurd (fun PP hP => ?_) h
    rw [hy PP hP, topL_rect hb ha, Matrix.det_one]
    exact ⟨lowZero_rect _ _ _, isUnit_one⟩

theorem stepVec_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Datum.EAf D)} {βT : GL (Fin T.rank) (Datum.EAf D)} {L : LevDat D.host.E ℂ S.rank}
    {χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {Q : Finset (Pl D.host.E)}
    {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT)
    (hr : S.rank ≤ T.rank) (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT L χ Q ξ f₀ f) :
    IsThetaFunO ψ S T f ∧ f ≠ 0 ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := by
  classical
  obtain ⟨hv, e, he', ⟨Tm, hTm⟩, hall⟩ := h
  obtain ⟨P, he, hP⟩ : ∃ P, IsIdemSum e P ∧ ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ Q :=
    ⟨_, he', fun PP => Finset.mem_union⟩
  have h0 : f₀ ≠ 0 := by
    rintro rfl
    obtain ⟨⟨p, hp⟩, h2⟩ := hv.2.norm
    have := h2 p hp
    simp [nrm2] at this
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS dS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT dT) βS βT
  have hSB := GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
      (GlobalTheory.PlaceDatum.exists_den_frMapO dS.1.fg dT.1.fg βS βT)
      ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ P
      (fun y => omegaG L χ y * omegaQ Q L.r ξ 1 y) fun y y' h => by
        rw [GlobalTheory.PlaceDatum.omegaG_congr _ _ y y' fun PP hPP => h PP ((hP PP).2 (Or.inl hPP)),
          GlobalTheory.PlaceDatum.omegaQ_congr _ _ _ 1 y y' fun PP hPP => h PP ((hP PP).2 (Or.inr hPP))]
  obtain ⟨k1, k2⟩ := GlobalTheory.Chain.StepVac.placeModel_span_ne hv.1 dS dT (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 hinf hTm hSB
  rw [← hall Tm hTm] at k1 k2
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 k1
  refine ⟨?_, k2 h0 fun hz => ?_, fun τ => ?_⟩
  · rw [← hc]
    exact GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hv.1.1 f₀ hv.2.theta _ c.support (fun a => a.1) c fun a _ => a.2
  · obtain ⟨x, h1, h2, h3⟩ := exists_rect S T βS βT he
    have := congrFun hz x
    rw [if_pos ⟨h1, h2⟩] at this
    exact mul_ne_zero (omegaG_ne_zero hr L χ _ fun PP h => h3 PP ((hP PP).2 (Or.inl h)))
      (omegaQ_ne_zero L.hr (L.hr.trans hr) Q ξ 1 _ fun PP h => h3 PP ((hP PP).2 (Or.inr h))) this
  · rw [← hc]
    exact GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hv.1.1 hv.2.inf f₀ hv.2.theta τ _ (hv.2.fock τ) _ c.support
      (fun a => a.1) c fun a _ => a.2

end GlobalTheory.InnerSteps

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerNormOneFiniteAdeleDetClass
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.FullDt

attribute [local instance] rlt_top rlt_topRing adeles_t2Space

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {SG SQ : Finset (HeightOneSpectrum (𝓞 H.E))}

theorem lift_mem_KDq (hl : LevOk H SG SQ) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (b : GlobalTheory.Mem.Chr.Ideles H.E)
    (hb : IsDetLift (host_cmData R H) x.1 b) (c : 𝓞 H.E) (hc : ∀ P ∈ uSG SG SQ, c ∈ P.asIdeal) (s : AfE H.F H.E)
    (hs : s ∈ RInt H.F H.E)
    (hx : ((x.1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 =
      1 + iA H.F H.E (algebraMap (𝓞 H.E) H.E c) * s) : b ∈ KDq H SQ := by
  have hd : ((x.1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)).det =
      1 + iA H.F H.E (algebraMap (𝓞 H.E) H.E c) * s := by
    rw [Matrix.det_fin_one, hx]
  have hdd := DetLift.det_mul_conj_det _ _ x.2
  set d := ((x.1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)).det with hdef
  have hci : ∀ w : HeightOneSpectrum (𝓞 H.E), adAt H.F w (iA H.F H.E (algebraMap (𝓞 H.E) H.E c)) =
      algebraMap H.E _ (algebraMap (𝓞 H.E) H.E c) := fun w => adAt_inclE H.F w _
  have hsv : ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (adAt H.F w s) ≤ 1 := (mem_rInt_iff H.F H.E s).1 hs
  have hle : ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (adAt H.F w d) ≤ 1 := fun w => by
    rw [hd, map_add (f := _), map_one, map_mul, hci]
    refine Valuation.map_add_le _ (by rw [map_one]) ?_
    rw [map_mul, valued_algebraMap]
    exact mul_le_one' (HeightOneSpectrum.valuation_le_one _ _) (hsv w)
  have hv1 : ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (adAt H.F w d) = 1 := fun w => by
    have e := congrArg (fun z => Valued.v (adAt H.F w z)) hdd
    simp only [map_mul, map_one] at e
    refine le_antisymm (hle w) ?_
    have e' : Valued.v (adAt H.F w d) * Valued.v (adAt H.F (conjPrime₂ w) d) = 1 := by
      rw [← valued_sigR (host_cmData R H) w d]
      exact e
    calc (1 : _) = Valued.v (adAt H.F w d) * Valued.v (adAt H.F (conjPrime₂ w) d) := e'.symm
      _ ≤ _ := mul_le_of_le_one_right' (hle _)
  have hcomp := fun w => DetSpec.compAt_eq hb w
  refine mem_KDq_of_conj hl b (fun w => ?_) fun P hP => ?_
  · rw [hcomp w, map_mul, hv1 w, one_mul, valued_sigR, adAt_finAf]
  · have h0 : adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E b : AfE H.F H.E)) ≠ 0 := by
      rw [← (Valued.v : Valuation (P.adicCompletion H.E) _).ne_zero_iff, valued_sigR, adAt_finAf]
      exact DetSpec.val_compAt_ne _ _
    rw [hcomp P, mul_div_cancel_right₀ _ h0]
    show Valued.v (adAt H.F P d - 1) < 1
    rw [hd, map_add (f := _), map_one, add_sub_cancel_left, map_mul, hci, map_mul,
      valued_algebraMap]
    have hlt : P.valuation H.E (algebraMap (𝓞 H.E) H.E c) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem P c).2 (hc P hP)
    exact (mul_le_of_le_one_right' (hsv P)).trans_lt hlt

theorem isOpen_ker_u1Dt : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SG SQ : Finset (HeightOneSpectrum (𝓞 H.E))), LevOk H SG SQ → letI := Formalism.BasicNotions.tensTopL (F := H.F) (E := H.E) (Formalism.L2.Herm.Af H.F); IsOpen {x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) | u1Dt H SQ x = 1} := by
  intro R H SG SQ hl
  classical
  obtain ⟨a, ha0, ha⟩ := rlt_exists_a (uSG SG SQ)
  set c : AfE H.F H.E := iA H.F H.E (algebraMap (𝓞 H.E) H.E a)⁻¹ with hc'
  have hca : iA H.F H.E (algebraMap (𝓞 H.E) H.E a) * c = 1 := by
    rw [hc', ← map_mul, mul_inv_cancel₀ (by simpa using ha0), map_one]
  let W : Set (GL (Fin 1) (AfE H.F H.E)) :=
    {u | c * ((u : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 - 1) ∈ Formalism.L2.Herm.intAf H.F H.E}
  have hWo : IsOpen W := by
    exact rlt_isOpen_intAf.preimage
      (continuous_const.mul ((Units.continuous_val.matrix_elem 0 0).sub continuous_const))
  have hW1 : (1 : GL (Fin 1) (AfE H.F H.E)) ∈ W := by
    show c * (((1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 - 1) ∈ Formalism.L2.Herm.intAf H.F H.E
    simp
  have hsub : ∀ x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H), x.1 ∈ W → x ∈ (u1Dt H SQ).ker := by
    intro x hx
    obtain ⟨b, hb⟩ := exists_lift H x
    rw [MonoidHom.mem_ker, normOneFiniteAdeleDetClass_of_isDetLift H SQ x b hb]
    refine (QuotientGroup.eq_one_iff b).2 (lift_mem_KDq hl x b hb a ha _ hx ?_)
    rw [← mul_assoc, hca, one_mul]
    ring
  have hnh : (((u1Dt H SQ).ker : Subgroup _) : Set (Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H))) ∈ 𝓝 (1 : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) := by
    have hpre : (fun x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) => x.1) ⁻¹' W ∈ 𝓝 (1 : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) :=
      (hWo.preimage continuous_subtype_val).mem_nhds hW1
    exact Filter.mem_of_superset hpre fun x hx => hsub x hx
  exact Subgroup.isOpen_of_mem_nhds _ hnh

end GlobalTheory.Mem.Col2.FullDt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotMemUnderLevelPrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LevTwist

theorem T_notMem_under_uSG : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok → ∀ (u : B.Word)
    (P : HeightOneSpectrum (𝓞 B.host.E)), P ∈ uSG (B.primes X).vGs I.SQ →
    (B.T u : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
  classical
  intro B X I hI u P hP hm
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hE : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := by
    have h1 : ((B.T u : ℕ) : 𝓞 B.host.F) ∈ P.asIdeal.under (𝓞 B.host.F) := hm
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
    exact h1
  rcases Finset.mem_union.1 hP with h | h
  · exact T_notMem_vGs hPr u ⟨P, h⟩ hE
  · have hg := (good_of_mem hI h).2
    have e := (ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.T_prime u)).2 hE
    refine hg.2.2 ?_
    rw [e]
    exact hI.T_mem u

end GlobalTheory.Mem.LevTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchrodingerIntertwinerInjectiveSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceModelInj

theorem placeModel_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (e : AE D) (f₀ Φ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → e * e = e → e * cA D e = 0 → infPart D e = 0 → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → f₀ ≠ 0 → IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ → Φ ≠ 0 → Tm Φ ≠ 0 :=
  fun _ _ _ _ _ _ _ _ _ _ hψ hS hT he hec hinf hTm hf hΦ h0 =>
    (GlobalTheory.Chain.StepVac.placeModel_span_ne hψ hS hT he hec hinf hTm hΦ).2 hf h0

end GlobalTheory.PlaceModelInj
end

