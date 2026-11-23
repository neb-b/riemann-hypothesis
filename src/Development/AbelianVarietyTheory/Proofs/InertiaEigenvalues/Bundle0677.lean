module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0622
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
public import Formalism.LocalRingCardinality.SpanPowerMembership
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAdjointChartBijectiveConjugateHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DownLift.ReadAdj

open GlobalTheory.AdelicLatMove

variable {D : D7}

theorem toEAf_onto : Function.Surjective (toEAf D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul x a => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

theorem cF_cF (z : Formalism.IndefR.Datum.EAf D) : cF D (cF D z) = z := by
  obtain ⟨a, rfl⟩ := toEAf_onto z
  exact GlobalTheory.PlaceVec.cF_cF_toEAf a

theorem frMapAdj_smul_eq (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (a : AE D)
    (x : WO S T) : frMapAdj S T βS βT (a • x) = toEAf D (cA D a) • frMapAdj S T βS βT x := by
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.frMapAdj_eq]
  have : (((a • x : WO S T).map (toEAf D)).map (cF D))ᵀ = toEAf D (cA D a) • ((x.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul, toEAf_cA]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_half (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) {e : AE D}
    {x : WO S T} (hx : IsHalf (cA D e) x) : toEAf D e • frMapAdj S T βS βT x = frMapAdj S T βS βT x := by
  conv_rhs => rw [← (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx]
  rw [frMapAdj_smul_eq, GlobalTheory.DualPairCheck.cA_cA]

theorem frMapAdj_sub (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (x y : WO S T) :
    frMapAdj S T βS βT (x - y) = frMapAdj S T βS βT x - frMapAdj S T βS βT y := by
  have h := GlobalTheory.PlaceVec.frMapAdj_add S T βS βT (x - y) y
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem frMapAdj_eq_zero (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) {x : WO S T}
    (h : frMapAdj S T βS βT x = 0) : x.map (toEAf D) = 0 := by
  have h1 := congrArg (fun N => (S.gram.map (eToEAf D) * βS.val) * N * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D))) h
  simp only [Matrix.mul_zero, Matrix.zero_mul] at h1
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.sandwich_cancel _ _ _ _ _ _ _ _ _ βS.mul_inv
    (GlobalTheory.PlaceVec.gram_map_mul_inv S) βT.mul_inv (GlobalTheory.PlaceVec.gram_map_mul_inv T)] at h1
  ext i j
  have h2 := congrFun (congrFun h1 j) i
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.zero_apply] at h2
  have h3 := congrArg (cF D) h2
  rw [cF_cF, map_zero] at h3
  simpa using h3

theorem phi_toEAf_idem {e : AE D} (he : e * e = e) {F : Type} [CommRing F] (φ : Formalism.IndefR.Datum.EAf D →+* F)
    (hker : ∀ z, φ z = 0 ↔ toEAf D e * z = 0) : φ (toEAf D e) = 1 := by
  have h : toEAf D e * (toEAf D e - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, he, sub_self]
  have := (hker _).2 h
  rw [map_sub, map_one, sub_eq_zero] at this
  exact this

theorem finPart_eq_zero_of_toEAf {a : AE D} (h : toEAf D a = 0) : finPart D a = 0 :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective (by rw [map_zero]; exact h)

theorem gram_inv_map_mul (S : HSp D) : (S.gram⁻¹).map (eToEAf D) * S.gram.map (eToEAf D) = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.PlaceVec.gram_map_mul_inv S)

theorem rdAdj_read : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D))
    (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)),
    Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι →
    (∀ m, ∃ x : WO S T, IsHalf (cA D e) x ∧ rdAdj S T βS βT φ x = m) ∧
    (∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → rdAdj S T βS βT φ x = rdAdj S T βS βT φ x' → x = x') ∧
    (∀ x : WO S T, IsHalf (cA D e) x → (IsIntM (frMapAdj S T βS βT x) ↔
      ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v),
        rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))) ∧
    ∀ (x : WO S T) (z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v)), IsIntM (frMapAdj S T βS βT x) →
      rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) →
      (redM PP (frMapAdj S T βS βT x)).map ι = z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) := by
  intro D S T βS βT e PP v φ ι hI hL
  obtain ⟨hsurj, hker, hint, hred⟩ := hL
  have hs : IsSplitIdem D e := hI.1
  have hc : IsSplitIdem D (cA D e) := GlobalTheory.SplitScalar.isSplitIdem_conj hs
  have h1 : φ (toEAf D e) = 1 := phi_toEAf_idem hs.1 φ hker
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    choose N hN using fun i j => hsurj (m i j)
    set Q : Matrix (Fin S.rank) (Fin T.rank) (Formalism.IndefR.Datum.EAf D) :=
      (S.gram.map (eToEAf D) * βS.val) * Matrix.of N * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D)) with hQ
    choose w hw using fun (i : Fin T.rank) (j : Fin S.rank) => toEAf_onto (Q j i)
    set x' : WO S T := Matrix.of fun i j => cA D (w i j) with hx'
    have hfx : frMapAdj S T βS βT x' = Matrix.of N := by
      rw [GlobalTheory.PlaceVec.frMapAdj_eq]
      have hX : ((x'.map (toEAf D)).map (cF D))ᵀ = Q := by
        ext i j
        simp only [Matrix.transpose_apply, Matrix.map_apply, hx', Matrix.of_apply, toEAf_cA, cF_cF, hw]
      rw [hX, hQ]
      exact GlobalTheory.PlaceVec.sandwich_cancel _ _ _ _ _ _ _ _ _ (gram_inv_map_mul S) βS.inv_mul (gram_inv_map_mul T)
        βT.inv_mul
    refine ⟨cA D e • x', fun i j => ?_, ?_⟩
    · show cA D e * (cA D e * x' i j) = cA D e * x' i j
      rw [← mul_assoc, hc.1]
    · ext i j
      simp only [rdAdj, Matrix.map_apply, frMapAdj_smul_eq, GlobalTheory.DualPairCheck.cA_cA, hfx, Matrix.smul_apply,
        smul_eq_mul, map_mul, Matrix.of_apply, hN]
      rw [show φ (toEAf D e) = 1 from h1, one_mul]
  · intro x x' hx hx' h
    have hd : IsHalf (cA D e) (x - x') := fun i j => by
      show cA D e * (x i j - x' i j) = x i j - x' i j
      rw [mul_sub, hx i j, hx' i j]
    have h0 : frMapAdj S T βS βT (x - x') = 0 := by
      ext i j
      have e1 := congrFun (congrFun h i) j
      simp only [rdAdj, Matrix.map_apply] at e1
      have e2 : φ (frMapAdj S T βS βT (x - x') i j) = 0 := by
        rw [frMapAdj_sub, Matrix.sub_apply, map_sub, e1, sub_self]
      have e3 := (hker _).1 e2
      have e4 := congrFun (congrFun (frMapAdj_half S T βS βT hd) i) j
      rw [Matrix.smul_apply, smul_eq_mul, e3] at e4
      rw [← e4, Matrix.zero_apply]
    have hf := frMapAdj_eq_zero S T βS βT h0
    have hinf := GlobalTheory.SplitScalar.half_fin hc hd
    ext i j
    refine sub_eq_zero.1 (GlobalTheory.SplitScalar.adele_ext ?_ ?_)
    · have := congrFun (congrFun hinf i) j
      rw [map_zero]; exact this
    · rw [map_zero]
      exact finPart_eq_zero_of_toEAf (congrFun (congrFun hf i) j)
  · intro x hx
    have hh := fun i j => congrFun (congrFun (frMapAdj_half S T βS βT hx) i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hh
    constructor
    · intro hI'
      refine ⟨Matrix.of fun i j => ⟨φ (frMapAdj S T βS βT x i j), (hint _).1 (by rw [hh i j]; exact hI' i j)⟩, ?_⟩
      ext i j
      rfl
    · rintro ⟨z, hz⟩ i j
      have e1 := congrFun (congrFun hz i) j
      simp only [rdAdj, Matrix.map_apply] at e1
      have e2 : φ (frMapAdj S T βS βT x i j) ∈ v.adicCompletionIntegers D.host.F := by
        rw [e1]; exact (z i j).2
      rw [← hh i j]
      exact (hint _).2 e2
  · intro x z hI' hz
    ext i j
    have e1 := congrFun (congrFun hz i) j
    simp only [rdAdj, Matrix.map_apply] at e1
    simp only [Matrix.map_apply, redM, dif_pos (hI' i j)]
    exact hred ⟨_, hI' i j⟩ (z i j) e1.symm

end GlobalTheory.DownLift.ReadAdj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasHodgeTateWeightFrameCharacterTwist
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
noncomputable section

namespace GlobalTheory.PMon.Twist

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def actM (g : GQ l) : P.R.BdR →* P.R.BdR := (P.actQdR g).toRingEquiv.toRingHom.toMonoidHom

theorem actM_apply (g : GQ l) (b : P.R.BdR) : actM P g b = P.actQdR g b := rfl

variable {P}

theorem unit_zpow_mem {u : P.R.BdRˣ} (h0 : (u : P.R.BdR) ∈ Fil P 0)
    (h1 : ((u⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0) (k : ℤ) : ((u ^ k : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0 := by
  induction k using Int.induction_on with
  | zero => rw [zpow_zero, Units.val_one]; exact one_mem_Fil
  | succ k ih => rw [zpow_add_one, Units.val_mul]; exact Fil_mul_left ih h0
  | pred k ih => rw [zpow_sub_one, Units.val_mul]; exact Fil_mul_left ih h1

theorem unitM_scal {n : Type} [Fintype n] [DecidableEq n] {U : GL n P.R.BdR} (hU : UnitM P U) {v : P.R.BdRˣ}
    (h0 : (v : P.R.BdR) ∈ Fil P 0) (h1 : ((v⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0) :
    UnitM P (scalGL n v * U) := by
  constructor
  · intro i j
    rw [scalGL_mul_val, Matrix.smul_apply, smul_eq_mul]
    exact Fil_mul_left h0 (hU.1 i j)
  · intro i j
    rw [mul_inv_rev, ← map_inv, ← (scalGL_commute n v⁻¹ U⁻¹).eq, scalGL_mul_val, Matrix.smul_apply, smul_eq_mul]
    exact Fil_mul_left h1 (hU.2 i j)

end GlobalTheory.PMon.Twist

namespace GlobalTheory.PMon.Twist

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem frame_scal {n : Type} [Fintype n] [DecidableEq n] {K K' : FinExt l} (hK : K.1 ≤ K'.1)
    (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (a : ℤ) (m : ℕ) (v : n → ℤ) (d : ℤ)
    (U : GL n P.R.BdR) (hU : ∀ g : ↥(GK K), matD P ρ m g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
      (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ v j : ℚ_[l]ˣ) : ℚ_[l]))
    (u : P.R.BdRˣ) (hu : ∀ g : ↥(GK K'), P.actQdR (g : GQ l) (u : P.R.BdR) =
      kd P (fr l m (χ g : ↥(MaximalUnramifiedExtension l))) * algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (-d) : ℚ_[l]ˣ) : ℚ_[l]) * u)
    (g : ↥(GK K')) :
    matD P (twist hK ρ χ a) m g *
        ((scalGL n (u ^ (-a)) * U : GL n P.R.BdR) : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
      ((scalGL n (u ^ (-a)) * U : GL n P.R.BdR) : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (v j + d * a) : ℚ_[l]ˣ) : ℚ_[l]) := by
  set F : P.R.BdRˣ := Units.map (kd P).toMonoidHom (Units.map (fr l m).toMonoidHom (χ g)) with hFdef
  set Q : P.R.BdRˣ := Units.map (algebraMap ℚ_[l] P.R.BdR).toMonoidHom (P.χQ (g : GQ l)) with hQdef
  have hF : ∀ k : ℤ, ((F ^ k : P.R.BdRˣ) : P.R.BdR) = kd P (fr l m ((χ g ^ k : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l))) := by
    intro k
    have : F ^ k = Units.map (kd P).toMonoidHom (Units.map (fr l m).toMonoidHom (χ g ^ k)) := by
      simp only [hFdef, map_zpow]
    rw [this]; rfl
  have hQ : ∀ k : ℤ, ((Q ^ k : P.R.BdRˣ) : P.R.BdR) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ k : ℚ_[l]ˣ) : ℚ_[l]) := by
    intro k
    have : Q ^ k = Units.map (algebraMap ℚ_[l] P.R.BdR).toMonoidHom (P.χQ (g : GQ l) ^ k) := by
      simp only [hQdef, map_zpow]
    rw [this]; rfl
  have hu' : Units.map (actM P (g : GQ l)) u = F * Q ^ (-d) * u := by
    apply Units.ext
    rw [Units.coe_map, actM_apply, hu g, Units.val_mul, Units.val_mul, hQ]
    have := hF 1
    rw [zpow_one, zpow_one] at this
    rw [this]
  have hs : P.actQdR (g : GQ l) ((u ^ (-a) : P.R.BdRˣ) : P.R.BdR) = (((F * Q ^ (-d) * u) ^ (-a) : P.R.BdRˣ) : P.R.BdR) := by
    rw [← hu', ← map_zpow, Units.coe_map, actM_apply]
  have hmat : matD P (twist hK ρ χ a) m g =
      ((F ^ a : P.R.BdRˣ) : P.R.BdR) • matD P ρ m ⟨g, GK_le hK g.2⟩ := by
    ext i j
    simp only [matD, twist_val, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hF]
  have hmap : ∀ (s : P.R.BdR) (M : Matrix n n P.R.BdR),
      (s • M).map (P.actQdR (g : GQ l)) = P.actQdR (g : GQ l) s • M.map (P.actQdR (g : GQ l)) := by
    intro s M
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have hdiag : (Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (v j + d * a) : ℚ_[l]ˣ) : ℚ_[l])) =
      ((Q ^ (d * a) : P.R.BdRˣ) : P.R.BdR) • Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ v j : ℚ_[l]ˣ) : ℚ_[l]) := by
    rw [hQ, ← Matrix.diagonal_smul]
    congr 1
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, zpow_add, Units.val_mul, map_mul]
    exact mul_comm _ _
  rw [hmat, scalGL_mul_val, hmap, hs, hdiag, smul_mul_smul_comm, smul_mul_smul_comm]
  have hUg := hU ⟨g, GK_le hK g.2⟩
  rw [hUg, ← Units.val_mul, ← Units.val_mul]
  congr 2
  rw [mul_zpow, mul_zpow, ← zpow_mul, neg_mul_neg, ← mul_assoc, ← mul_assoc, ← zpow_add, add_neg_cancel,
    zpow_zero, one_mul, mul_comm]

end GlobalTheory.PMon.Twist

namespace GlobalTheory.PMon.Twist


set_option maxHeartbeats 1000000 in
theorem framed_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type)
    [Fintype n] [DecidableEq n] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r N : ℕ) (hr : 0 < r)
    (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (x : P.R.Bˣ) (a : ℤ),
    IsRat r ρ → Framed P ρ w →
    (∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) →
    P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < r * N → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) →
    Framed P (GlobalTheory.PMon.Twist.twist hK ρ χ a)
      (fun (m : Fin (r * N)) j => w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩ j + if (m : ℕ) = 0 then a else 0) := by
  intro l _ P AI T n _ _ K K' hK r N hr ρ w χ x a hρ hf hx hx1 hx2 hev m
  obtain ⟨-, -, hshift, hunit, -⟩ := _root_.GlobalTheory.PMon.bdR_tied l P AI T
  have hgal : ∀ g : ↥(GK K'), P.actQdR (g : GQ l) (ev P m x) = kd P (fr l m (χ g : ↥(MaximalUnramifiedExtension l))) * ev P m x := by
    intro g
    rw [← ev_act, hx g, ← evHom_apply, map_mul, evHom_apply, evHom_apply, ev_kur]
  obtain ⟨e, he0, he1, hegal⟩ : ∃ e : P.R.BdR, e ∈ Fil P 0 ∧ e ∉ Fil P 1 ∧ ∀ g : ↥(GK K'),
      P.actQdR (g : GQ l) e = kd P (fr l m (χ g : ↥(MaximalUnramifiedExtension l))) *
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (-(if (m : ℕ) = 0 then 1 else 0 : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * e := by
    by_cases hm : (m : ℕ) = 0
    · have e0 : ev P (m : ℕ) x = P.ιB x := by rw [hm]; rfl
      refine ⟨tz P (-1) * ev P m x, ?_, ?_, fun g => ?_⟩
      · have h := (hshift 1 (-1) (P.ιB x)).1 hx1
        rw [show (1 : ℤ) + -1 = 0 by norm_num] at h
        rwa [e0]
      · intro h
        rw [e0] at h
        apply hx2
        refine (hshift 2 (-1) (P.ιB x)).2 ?_
        rwa [show (2 : ℤ) + -1 = 1 by norm_num]
      · rw [if_pos hm, map_mul, GlobalTheory.PMon.Model.act_tz, hgal g]
        ring
    · have hj := hev m (Nat.pos_of_ne_zero hm) m.2
      refine ⟨ev P m x, hj.1, hj.2, fun g => ?_⟩
      rw [if_neg hm, hgal g, neg_zero, zpow_zero, Units.val_one, map_one, mul_one]
  obtain ⟨y, hy0, hey⟩ := hunit e he0 he1
  let u : P.R.BdRˣ := ⟨e, y, hey, by rw [mul_comm]; exact hey⟩
  have hu0 : (u : P.R.BdR) ∈ Fil P 0 := he0
  have hu1 : ((u⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0 := hy0
  obtain ⟨U, hUm, hU⟩ := hf ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩
  have hper : ∀ g, matD P ρ m g = matD P ρ ((m : ℕ) % r) g := fun g => by
    ext i j
    simp only [matD, Matrix.map_apply]
    rw [fr_mod (hρ.rat g i j)]
  refine ⟨scalGL n (u ^ (-a)) * U, unitM_scal hUm (unit_zpow_mem hu0 hu1 _)
    (by rw [← zpow_neg]; exact unit_zpow_mem hu0 hu1 _), fun g => ?_⟩
  have key := frame_scal hK ρ χ a m (w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩) (if (m : ℕ) = 0 then 1 else 0) U
    (fun g' => by rw [hper]; exact hU g') u hegal g
  have hda : (if (m : ℕ) = 0 then (1 : ℤ) else 0) * a = if (m : ℕ) = 0 then a else 0 := by
    split_ifs <;> simp
  simp only [hda] at key
  exact key

end GlobalTheory.PMon.Twist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoStatement
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.HyodoDef TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem hyodo : Hyodo := by
  intro l _ P AI T K V _ _ _ _ _ ρ hcont hsst c hc hcoc hdR
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  haveI : ContinuousSMul ℚ_[l] V := IsModuleTopology.toContinuousSMul ℚ_[l] V
  obtain ⟨ρ', m, hρ'c, hdual⟩ := _root_.GlobalTheory.DualTwist.exists_dual1 l P K V ρ hcont
  have hdrV : IsDR (P.PD K) ρ := _root_.GlobalTheory.sst_isDR l P AI T K V ρ hsst
  have hdrV' : IsDR (P.PD K) ρ' := by
    letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
    haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    exact (_root_.GlobalTheory.TateDualTied.main l P AI T K).1 ℚ_[l] ℤ_[l] GlobalTheory.Published.BlochKato.goodO_padicInt
      { V := V, ρ := ρ, cont := hcont } { V := Fin (finrank ℚ_[l] V) → ℚ_[l], ρ := ρ', cont := hρ'c } m hdrV hdual
  have hfin : Module.Finite ℚ_[l] ↥(continuousCocycles ρ) := _root_.GlobalTheory.HyodoFin.finite_continuous_cocycles_localGaloisRep l P K V ρ hcont
  obtain ⟨S, _hfS, hSc, hSst, hSdR, hS⟩ := GlobalTheory.T.semistable_cocycles_between_blochKato_and_continuous l P AI T K V _ ρ ρ' m hcont hdual hsst hfin
  have hgc : geometricCocycles (P.PD K) ρ ≤ continuousCocycles ρ := fun _ h => h.1
  haveI : Module.Finite ℚ_[l] ↥(geometricCocycles (P.PD K) ρ) :=
    Module.Finite.of_injective (Submodule.inclusion hgc) (Submodule.inclusion_injective hgc)
  have hSg : S ≤ geometricCocycles (P.PD K) ρ := fun c hc => ⟨hSc hc, hSdR c hc⟩
  have h1 := _root_.GlobalTheory.HyodoDef.Count.finrank_blochKato_g_add_e_le_f_add_f_alt l P AI T K V ρ _ ρ' m hcont hρ'c hdrV hdrV' hdual
  have h2 := GlobalTheory.T.finrank_finite_le_exponential_cocycles l P AI T K _ ρ' hρ'c hdrV'
  have hEq : S = geometricCocycles (P.PD K) ρ := Submodule.eq_of_le_of_finrank_le hSg (by omega)
  have hcg : c ∈ geometricCocycles (P.PD K) ρ := ⟨⟨hc, hcoc⟩, hdR⟩
  rw [← hEq] at hcg
  exact hSst c hcg

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvMemDeRhamFilNegOfExactDegree
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.FilInv

theorem pow_mem_Fil {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {b : ℤ} {x : BdR} (hx : x ∈ PD.Fil b) (n : ℕ) :
    x ^ n ∈ PD.Fil (n * b) := by
  induction n with
  | zero => simpa using PD.one_mem
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact PD.Fil_mul _ _ _ _ ih hx

theorem inv_mem_Fil_neg : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (a : ℤ) (u v : P.R.BdR), u * v = 1 → u ∈ (P.PD K).Fil a → u ∉ (P.PD K).Fil (a + 1) → v ∈ (P.PD K).Fil (-a) := by
  intro l _ P AI T K a u v huv hu hu1
  obtain ⟨s, hs, hts⟩ := GlobalTheory.TopSteps.CrysRules.exists_inverse_fontaineElement_mem_fil_neg_one T K
  have ht := (P.PD K).mem_filtration_one

  obtain ⟨w, w', hw, hw', hww⟩ : ∃ w w' : P.R.BdR, w ∈ (P.PD K).Fil (-a) ∧ w' ∈ (P.PD K).Fil a ∧
      w * w' = 1 := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a
    · refine ⟨s ^ n, ((P.PD K).ι (P.PD K).t) ^ n, ?_, ?_, ?_⟩
      · simpa using pow_mem_Fil (P.PD K) hs n
      · simpa using pow_mem_Fil (P.PD K) ht n
      · rw [← mul_pow, mul_comm, hts, one_pow]
    · refine ⟨((P.PD K).ι (P.PD K).t) ^ n, s ^ n, ?_, ?_, ?_⟩
      · simpa using pow_mem_Fil (P.PD K) ht n
      · simpa using pow_mem_Fil (P.PD K) hs n
      · rw [← mul_pow, hts, one_pow]
  have hx0 : u * w ∈ (P.PD K).Fil 0 := by
    simpa using (P.PD K).Fil_mul _ _ _ _ hu hw
  have hx1 : u * w ∉ (P.PD K).Fil 1 := by
    intro h
    apply hu1
    have := (P.PD K).Fil_mul _ _ _ _ h hw'
    rwa [mul_assoc, hww, mul_one, add_comm] at this
  obtain ⟨y, hy, hxy⟩ := ((GlobalTheory.Per.TiedField.tied_field l P AI T).2.2.2.2) K _ hx0 hx1
  have hv : v = w * y := by
    calc v = v * ((u * w) * y) := by rw [hxy, mul_one]
      _ = (u * v) * (w * y) := by ring
      _ = w * y := by rw [huv, one_mul]
  rw [hv]
  simpa using (P.PD K).Fil_mul _ _ _ _ hw hy

end GlobalTheory.FilInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGapNonemptyAndRecordNonempty
section
open Formalism Formalism.BasicNotions
namespace GlobalTheory.MemLoc

theorem localGap_nonempty : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R),
    Nonempty (Formalism.BasicNotions.Examples₂.LocalGap H) := by
  intro R H
  obtain ⟨L, A, ⟨T⟩⟩ := exists_locTheory_tied
  exact ⟨⟨L, A, T⟩⟩

theorem record_nonempty : Nonempty Formalism.BasicNotions.D7 :=
  Formalism.BasicNotions.Examples₂.record_nonempty_of_localGap (localGap_nonempty _)

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardModulePropertiesStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_module_properties : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.LanglandsMultisegments →
    ∀ (P : Segment k → Prop), (∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, P Δ) → ∃ y : IrrGL (k := k), IsL 𝔫 y.rep) →
    ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (𝔪 : Fin h → Multiset (Segment k)),
      (∀ j, IsL (𝔪 j) (x j).rep) → (∀ j, ∀ Δ ∈ 𝔪 j, P Δ) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), π.IsIrreducible →
        Nonempty (π.Equiv (prodIrr x hd)) → IsL (∑ j, 𝔪 j) π := by
  first | exact @GlobalTheory.LocGL.IrrProdL.isL_sum_of_isIrreducible | exact GlobalTheory.LocGL.IrrProdL.isL_sum_of_isIrreducible | (intros; apply GlobalTheory.LocGL.IrrProdL.isL_sum_of_isIrreducible <;> assumption)
end

