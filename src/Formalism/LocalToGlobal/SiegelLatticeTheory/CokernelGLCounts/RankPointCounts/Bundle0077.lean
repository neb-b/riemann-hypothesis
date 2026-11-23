module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepPinExistsOfPlace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0071
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NotIntDensOfSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityUnderRingMap.MemIntegerOfIsIntegralMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualCountBound.HaarIdx
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealFrameCoordinates
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.RealFrameCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word)

def g0 (γ : X.B.I.Ginf) (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ (vOf X τ))

private theorem rdE_pos_rank_point_counts (D : D7) : 0 < D.host.rdE := by
  simp only [Formalism.BasicNotions.Host.rdE]
  apply Real.rpow_pos_of_pos
  rw [abs_pos]
  exact_mod_cast NumberField.discr_ne_zero (K := D.host.E)

private theorem frS_eq_inv_rdE (D : D7) : frS D = ((D.host.rdE : ℝ) : ℂ)⁻¹ := by
  have hne := (rdE_pos_rank_point_counts D).ne'
  have hpi := Real.pi_ne_zero
  have h : D.host.ka / (2 * Real.pi) = D.host.rdE⁻¹ := by
    simp only [Formalism.BasicNotions.Host.ka, Formalism.BasicNotions.Host.v]
    field_simp <;> ring
  simp only [frS, h, Complex.ofReal_inv]

private theorem rhoF_eq_frS_pow (D : D7) (a : Fin (D.R.rS + 1)) :
    ((rhoF D a : ℝ) : ℂ) = frS D ^ (D.R.rS - (a : ℕ)) := by
  have hpos := rdE_pos_rank_point_counts D
  have ha : (a : ℕ) ≤ D.R.rS := Nat.lt_succ_iff.mp a.isLt
  rw [frS_eq_inv_rdE]
  simp only [rhoF]
  rw [show (-((D.R.rS : ℝ) - ((a : ℕ) : ℝ))) = -(((D.R.rS - (a : ℕ) : ℕ) : ℝ)) by rw [Nat.cast_sub ha],
    Real.rpow_neg hpos.le, Real.rpow_natCast, Complex.ofReal_inv, Complex.ofReal_pow, inv_pow]

private theorem Q_mulVec_fvec_eq_smul_frm (τ : D.what₂.Tau) (a : Fin (D.R.rS + 1)) :
    C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a =
      ((rhoF D a : ℝ) : ℂ) • Formalism.L2.SG.RealObj.frm X u 1 (vOf X τ) a := by
  obtain ⟨-, h2, -, h4⟩ := C.isT τ
  induction a using Fin.lastCases with
  | last =>
    simp only [Formalism.QuantumDeterminants.fvec, Fin.val_last, lt_self_iff_false, dite_false, zB, Matrix.mulVec_mulVec, h2,
      Matrix.one_mulVec, rhoF_eq_frS_pow, Nat.sub_self, pow_zero, one_smul, Formalism.L2.SG.RealObj.frm,
      Formalism.L2.SG.RealObj.famSc, Formalism.L2.SG.RealObj.fam, Fin.snoc_last, Complex.ofReal_one, one_pow, inv_one]
  | cast i =>
    obtain ⟨hq, -⟩ := h4 i i rfl
    simp only [Formalism.QuantumDeterminants.fvec, Fin.coe_castSucc, i.isLt, dite_true, Fin.eta, Formalism.QuantumDeterminants.bvec, hq, rhoF_eq_frS_pow,
      Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc, Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc,
      Complex.ofReal_one, one_pow, inv_one, one_smul]

private theorem herm_Hpk_eq_hJ_Q_mulVec (τ : D.what₂.Tau) (x y : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) x y =
      hJ (X.B.I.ε (vOf X τ)) (C.Q τ *ᵥ y) (C.Q τ *ᵥ x) := by
  obtain ⟨-, -, h3, -⟩ := C.isT τ
  rw [← h3]
  simp only [Formalism.QuantumDeterminants.herm, hJ, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

private theorem Q_mulVec_g0_mulVec_eq (γ : X.B.I.Ginf) (τ : D.what₂.Tau) (w : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) :
    C.Q τ *ᵥ ((g0 C γ τ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) *ᵥ w) =
      uMat (γ (vOf X τ)) *ᵥ (C.Q τ *ᵥ w) := by
  obtain ⟨-, h2, -, -⟩ := C.isT τ
  simp only [g0, Formalism.L2.SG.RealObj.trG, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem zhat_conjugator_scaled (γ : X.B.I.Ginf) (τ : D.what₂.Tau) (a b : Fin (D.R.rS + 1)) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (g0 C γ τ) a b =
      ((rhoF D a * rhoF D b : ℝ) : ℂ) * Formalism.L2.SG.RealObj.ZX X u u' 1 γ (vOf X τ) a b := by
  simp only [Formalism.QuantumDeterminants.Zhat]
  rw [herm_Hpk_eq_hJ_Q_mulVec C τ, Q_mulVec_g0_mulVec_eq C γ τ, Q_mulVec_fvec_eq_smul_frm C u τ, Q_mulVec_fvec_eq_smul_frm C u' τ]
  have hs : ∀ x : ℝ, star (x : ℂ) = (x : ℂ) := fun x => Complex.conj_ofReal x
  simp only [Formalism.L2.SG.RealObj.ZX, Formalism.L2.SG.RealObj.Zhat, hJ, Matrix.mulVec_smul, star_smul, hs,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  push_cast
  ring

private theorem ptEntry_locBlocksFrom_eq (D : D7) (τ : D.what₂.Tau) :
    ∀ (L : List (D.host.E × ℕ)) (A i j : ℕ),
      ptEntry (locBlocksFrom D (rhoReal D) τ A L) i j =
        ((D.host.rdE ^ (-((D.R.rS : ℤ) - ((A + i : ℕ) : ℤ))) *
          D.host.rdE ^ (-((D.R.rS : ℤ) - ((A + j : ℕ) : ℤ))) : ℝ) : ℂ) * plEmb D τ (ptEntry L i j) := by
  have hne : D.host.rdE ≠ 0 := (rdE_pos_rank_point_counts D).ne'
  intro L
  induction L with
  | nil =>
    intro A i j
    simp only [locBlocksFrom, ptEntry, map_zero, mul_zero]
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    intro A i j
    simp only [locBlocksFrom, ptEntry]
    by_cases h1 : i < s ∧ j < s
    · rw [if_pos h1, if_pos h1]
      by_cases h2 : i + j + 1 = s
      · rw [if_pos h2, if_pos h2]
        have hz : rhoReal D (A + 1) s = D.host.rdE ^ (-((D.R.rS : ℤ) - ((A + i : ℕ) : ℤ))) *
            D.host.rdE ^ (-((D.R.rS : ℤ) - ((A + j : ℕ) : ℤ))) := by
          rw [← zpow_add₀ hne]
          simp only [rhoReal]
          congr 1
          push_cast
          omega
        rw [hz]
      · rw [if_neg h2, if_neg h2, map_zero, mul_zero]
    · rw [if_neg h1, if_neg h1]
      by_cases h3 : s ≤ i ∧ s ≤ j
      · rw [if_pos h3, if_pos h3, ih]
        obtain ⟨h3i, h3j⟩ := h3
        rw [show A + s + (i - s) = A + i by omega, show A + s + (j - s) = A + j by omega]
      · rw [if_neg h3, if_neg h3, map_zero, mul_zero]

theorem zhat_conjugator_eq_point (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (hrep : Formalism.L2.SG.RealObj.IsPtRep X u u' w γ)
    (τ : D.what₂.Tau) :
    ZhatO D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (g0 C γ τ) = ptMat (ptLoc D τ w) := by
  funext a b
  have hv : X.pl (vOf X τ) = τ := X.pl.apply_symm_apply τ
  have hpe : ∀ x, plEmb D τ x = embS D τ x := fun x => rfl
  have hρ : ∀ c : Fin (D.R.rS + 1), rhoF D c = D.host.rdE ^ (-((D.R.rS : ℤ) - ((c : ℕ) : ℤ))) := by
    intro c
    simp only [rhoF]
    rw [← Real.rpow_intCast]
    norm_num
  have hr := congrFun (congrFun (hrep (vOf X τ)) a) b
  simp only [Formalism.L2.SG.RealObj.ZhatO, Formalism.L2.SG.RealObj.ptC, Matrix.map_apply, X.φ_eq,
    RingEquiv.apply_symm_apply, hv, ptMat] at hr
  simp only [ZhatO, zhat_conjugator_scaled C u u' γ τ, ptMat, ptLoc, ptLocS, locBlocks, ptEntry_locBlocksFrom_eq, Nat.zero_add, hpe, hρ]
  rw [← hr]
  push_cast
  ring

theorem frS_mul_rd (D : D7) : frS D * (D.host.rdE : ℂ) = 1 := by
  rw [frS_eq_inv_rdE]
  exact inv_mul_cancel₀ (by exact_mod_cast (rdE_pos_rank_point_counts D).ne')

theorem rho_eq (D : D7) (b : Fin (D.R.rS + 1)) :
    ((rhoF D b : ℝ) : ℂ) = ((D.host.rdE : ℂ) ^ (D.R.rS - b.val))⁻¹ := by
  rw [rhoF_eq_frS_pow, frS_eq_inv_rdE, inv_pow]

theorem hpk_esI (k r : ℕ) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    (Formalism.QuantumDeterminants.Hpk k r *ᵥ v) (Formalism.QuantumDeterminants.esI k r a) = v (Formalism.QuantumDeterminants.eI k r a) := by
  have ha := a.isLt
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (Formalism.QuantumDeterminants.eI k r a)]
  · have h1 : Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.esI k r a) (Formalism.QuantumDeterminants.eI k r a) = 1 := by
      simp only [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.esI, Formalism.QuantumDeterminants.eI, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ a.val := fun h => hj (Fin.ext (by simp [Formalism.QuantumDeterminants.eI, h]))
    have h0 : Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.esI k r a) j = 0 := by
      simp only [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.esI, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

def cMg (γ : X.B.I.Ginf) (τ : D.what₂.Tau) (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  C.Qi τ * ((uMat (γ (vOf X τ)))⁻¹ * uMat y * uMat (γ (vOf X τ))) * C.Q τ

private theorem mulVec_apply_eq_herm_single {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ) (i : Fin m) :
    (H *ᵥ x) i = Formalism.QuantumDeterminants.herm H x (Pi.single i 1) := by
  have hs : star (Pi.single i 1 : Fin m → ℂ) = Pi.single i 1 := by
    ext j
    by_cases h : j = i <;> simp [Pi.single_apply, h]
  simp [Formalism.QuantumDeterminants.herm, hs, dotProduct, Pi.single_apply]

private theorem Q_mulVec_cMg_mulVec_eq (γ : X.B.I.Ginf) (τ : D.what₂.Tau) (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (f : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) :
    C.Q τ *ᵥ (cMg C γ τ y *ᵥ f) =
      ((uMat (γ (vOf X τ)))⁻¹ * uMat y * uMat (γ (vOf X τ))) *ᵥ (C.Q τ *ᵥ f) := by
  obtain ⟨-, h2, -, -⟩ := C.isT τ
  simp only [cMg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem stCoordV_eq (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (τ : D.what₂.Tau)
    (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (p : Formalism.L2.SG.RealObj.FreeE w) :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) y p =
      (cMg C γ τ y *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u' τ) p.1.2)
        (Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨p.1.1.1, by have := p.2.1; have := p.1.2.isLt; omega⟩) := by
  obtain ⟨-, -, -, h4⟩ := C.isT τ
  have hlt : p.1.1.1 < D.R.rS := by have := p.2.1; have := p.1.2.isLt; omega
  have hs : ∀ x : ℝ, star (x : ℂ) = (x : ℂ) := fun x => Complex.conj_ofReal x
  have hU : uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) =
      (uMat (γ (vOf X τ)))⁻¹ * uMat y * uMat (γ (vOf X τ)) := by
    simp [uMat, Matrix.coe_units_inv]
  have hc : (star (frS D ^ (D.R.rS - ((⟨p.1.1.1, hlt⟩ : Fin D.R.rS) : ℕ))))⁻¹ =
      (D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1) := by
    rw [frS_eq_inv_rdE, ← Complex.ofReal_inv, ← Complex.ofReal_pow, hs, Complex.ofReal_pow, Complex.ofReal_inv,
      inv_pow, inv_inv]
  obtain ⟨-, hf⟩ := h4 ⟨p.1.1.1, hlt⟩ ⟨p.1.1.1, hlt⟩ rfl
  rw [← hpk_esI D.R.k D.R.rS ⟨p.1.1.1, hlt⟩
      (cMg C γ τ y *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u' τ) p.1.2),
    mulVec_apply_eq_herm_single, herm_Hpk_eq_hJ_Q_mulVec C τ, hf, hc, Q_mulVec_cMg_mulVec_eq C γ τ, Q_mulVec_fvec_eq_smul_frm C u' τ]
  simp only [Formalism.L2.SG.NGPin.stCoordV, hU, rho_eq, Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc,
    Complex.ofReal_one, one_pow, inv_one, one_smul, hJ, Matrix.mulVec_smul, star_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hs, star_pow]
  ring

end Formalism.L2.SG.RealFrameCoordinates

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SRLiftFin
section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents.RF

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel PI.IntegralDiscriminantMembership

theorem finite_max_of {R : Type*} [CommRing R] (c : R) (hc : ∀ m : Ideal R, m.IsMaximal → c ∈ m)
    (hfin : Finite (R ⧸ Ideal.span {c})) : {m : Ideal R | m.IsMaximal}.Finite := by
  haveI := hfin
  haveI : Finite (Ideal (R ⧸ Ideal.span {c})) :=
    Finite.of_injective (fun I : Ideal (R ⧸ Ideal.span {c}) => (I : Set (R ⧸ Ideal.span {c}))) SetLike.coe_injective
  refine (Set.finite_univ.image (fun J : Ideal (R ⧸ Ideal.span {c}) => Ideal.comap (Ideal.Quotient.mk _) J)).subset ?_
  intro m hm
  refine ⟨Ideal.map (Ideal.Quotient.mk _) m, Set.mem_univ _, ?_⟩
  dsimp only
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem m).mpr (hc m hm))

theorem finite_max_of_equiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : {m : Ideal S | m.IsMaximal}.Finite) : {m : Ideal R | m.IsMaximal}.Finite := by
  refine (h.image (fun n : Ideal S => Ideal.comap e n)).subset ?_
  intro m hm
  haveI : m.IsMaximal := hm
  refine ⟨Ideal.map e m, Ideal.map_isMaximal_of_equiv e, ?_⟩
  first
  | exact Ideal.comap_map_of_bijective _ e.bijective
  | exact Ideal.comap_map_of_bijective e e.bijective
  | simp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem unit_one_sub (M : Model F E) (hOK : M.OK) (π : 𝒪[F]) (hπ : π ∈ nonunits 𝒪[F]) (r : M.L.O) :
    IsUnit (1 - (⟨algebraMap F E (π : F), (alg_mem_O M).mpr π.2⟩ : M.L.O) * r) := by
  have := hOK.loc
  haveI : IsLocalRing 𝒪[F] := inferInstance
  obtain ⟨⟨tr, htr⟩, ⟨nr, hnr⟩⟩ := (mem_O_iff M r).mp r.2
  set x : E := 1 - algebraMap F E (π : F) * r with hx
  have hcj : M.L.cj x = 1 - algebraMap F E (π : F) * M.L.cj r := by
    rw [hx, map_sub, map_one, map_mul, cj_alg]
  have hN : x * M.L.cj x = algebraMap F E ((1 : F) - (π : F) * ((tr : F) - (π : F) * (nr : F))) := by
    rw [hcj, hx]
    simp only [map_sub, map_one, map_mul]
    rw [htr, hnr]; ring
  set n : 𝒪[F] := 1 - π * (tr - π * nr) with hn
  have hnu : IsUnit n := by
    apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
    exact mul_mem_nonunits_left hπ
  obtain ⟨nu, hnu'⟩ := hnu
  have hNn : x * M.L.cj x = algebraMap F E (n : F) := by rw [hN, hn]; push_cast; ring_nf
  have hyO : M.L.cj x * algebraMap F E ((nu⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) ∈ M.L.O :=
    M.L.O.mul_mem (Formalism.L2.SG.Pf.Cnt.DualityBasisChange.cj_mem_O (M := M) x (by
      rw [hx]; exact M.L.O.sub_mem M.L.O.one_mem (M.L.O.mul_mem ((alg_mem_O M).mpr π.2) r.2)))
      ((alg_mem_O M).mpr (nu⁻¹ : 𝒪[F]ˣ).1.2)
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hyO⟩, Subtype.ext ?_⟩
  show x * (M.L.cj x * algebraMap F E ((nu⁻¹ : 𝒪[F]ˣ) : 𝒪[F])) = 1
  rw [← mul_assoc, hNn, ← map_mul, ← hnu']
  rw [show ((nu : 𝒪[F]) : F) * (((nu⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) = 1 by
    rw [← Subring.coe_mul, Units.mul_inv]; rfl, map_one]

theorem finite_max_O (M : Model F E) (hOK : M.OK) : {m : Ideal M.L.O | m.IsMaximal}.Finite := by
  have := hOK.loc
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  set c : M.L.O := ⟨algebraMap F E (π : F), (alg_mem_O M).mpr π.2⟩ with hc
  refine finite_max_of c (fun m hm => ?_) ?_
  · by_contra hcm
    have htop : m ⊔ Ideal.span {c} = ⊤ := hm.1.2 _ (lt_of_le_of_ne le_sup_left (fun h => hcm (h ▸
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self c))))
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : M.L.O) ∈ m ⊔ Ideal.span {c})
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    have hu := unit_one_sub M hOK π hπ.not_isUnit r
    have : a = 1 - c * r := by rw [← hab]; ring
    rw [this] at ha
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
  · have h := card_quot_pi M hOK π hπ
    have hq : 0 < qF F := Nat.card_pos (α := 𝓀[F])
    exact Nat.finite_of_card_ne_zero (by rw [h]; positivity)

section ModeG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem mem_R_some (M : Model F E) {g : SplitG M.L} (hs : M.split = some g) (x : E) :
    x ∈ M.R ↔ ∃ a b : 𝒪[F], g.e x = ((a : F), (b : F)) ∧
      Ideal.Quotient.mk (Ideal.span {g.q}) a = Ideal.Quotient.mk (Ideal.span {g.q}) b := by
  unfold Formalism.MainNotions.S.Loc.Model.R
  rw [hs]
  simp only [Subring.mem_comap, Subring.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hab, he⟩
    exact ⟨a, b, he.symm, hab⟩
  · rintro ⟨a, b, he, hab⟩
    exact ⟨(a, b), hab, he.symm⟩

theorem isUnit_of_fst (M : Model F E) (hOK : M.OK) {g : SplitG M.L} (hs : M.split = some g) (x : M.R)
    (a b : 𝒪[F]) (he : g.e x = ((a : F), (b : F)))
    (hab : Ideal.Quotient.mk (Ideal.span {g.q}) a = Ideal.Quotient.mk (Ideal.span {g.q}) b) (ha : IsUnit a) :
    IsUnit x := by
  have := hOK.loc
  haveI : IsLocalRing 𝒪[F] := inferInstance
  obtain ⟨s, hsq⟩ := Ideal.mem_span_singleton'.1 ((Ideal.Quotient.eq).1 hab.symm)
  have hqn : g.q ∈ nonunits 𝒪[F] := g.q_irr.not_isUnit
  have hqm : g.q ∈ IsLocalRing.maximalIdeal 𝒪[F] := (IsLocalRing.mem_maximalIdeal _).2 hqn
  have hb : IsUnit b := by
    by_contra hb
    have hbm : b ∈ IsLocalRing.maximalIdeal 𝒪[F] := (IsLocalRing.mem_maximalIdeal _).2 hb
    have ham : a ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
      have : a = b - s * g.q := by rw [hsq]; ring
      rw [this]
      exact Ideal.sub_mem _ hbm (Ideal.mul_mem_left _ _ hqm)
    exact (IsLocalRing.mem_maximalIdeal _).1 ham ha
  obtain ⟨ua, rfl⟩ := ha
  obtain ⟨ub, rfl⟩ := hb
  set y : E := g.e.symm (((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]), ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F])) with hy
  have hyR : y ∈ M.R := by
    rw [mem_R_some M hs]
    refine ⟨_, _, by rw [hy, AlgEquiv.apply_symm_apply], ?_⟩
    rw [Ideal.Quotient.eq]
    refine Ideal.mem_span_singleton'.2 ⟨((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * s, ?_⟩
    have h1 : ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * (ub : 𝒪[F]) = 1 := Units.inv_mul ub
    have h2 : ((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * (ua : 𝒪[F]) = 1 := Units.inv_mul ua
    have e1 : ((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) - ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) =
        ((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * ((ub : 𝒪[F]) - (ua : 𝒪[F])) := by
      linear_combination (-((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F])) * h1 + ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * h2
    rw [e1, ← hsq]; ring
  refine isUnit_iff_exists_inv.2 ⟨⟨y, hyR⟩, Subtype.ext ?_⟩
  show (x : E) * y = 1
  apply g.e.injective
  rw [map_mul, he, hy, AlgEquiv.apply_symm_apply, map_one]
  ext
  · show ((ua : 𝒪[F]) : F) * (((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) = 1
    rw [← Subring.coe_mul, Units.mul_inv]; rfl
  · show ((ub : 𝒪[F]) : F) * (((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) = 1
    rw [← Subring.coe_mul, Units.mul_inv]; rfl

theorem fst_isUnit (M : Model F E) {g : SplitG M.L} (hs : M.split = some g) (x : M.R) (hx : IsUnit x)
    (a b : 𝒪[F]) (he : g.e x = ((a : F), (b : F))) : IsUnit a := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨a', b', he', -⟩ := (mem_R_some M hs (((u⁻¹ : (M.R)ˣ) : M.R) : E)).mp ((u⁻¹ : (M.R)ˣ) : M.R).2
  have h1 : g.e ((((u : (M.R)ˣ) : M.R) : E) * (((u⁻¹ : (M.R)ˣ) : M.R) : E)) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one, map_one]
  rw [map_mul, he, he'] at h1
  have h2 : (a : F) * a' = 1 := congrArg Prod.fst h1
  exact ⟨⟨a, a', Subtype.ext (by push_cast; exact h2), Subtype.ext (by push_cast; rw [mul_comm]; exact h2)⟩, rfl⟩

theorem isLocal_R (M : Model F E) (hOK : M.OK) {g : SplitG M.L} (hs : M.split = some g) : IsLocalRing M.R := by
  have := hOK.loc
  haveI : IsLocalRing 𝒪[F] := inferInstance
  haveI : Nontrivial M.R := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 := congrArg (fun x : M.R => (g.e (x : E)).1) h
    simp at h1
  refine IsLocalRing.of_nonunits_add fun x y hx hy hxy => ?_
  obtain ⟨a, b, he, hab⟩ := (mem_R_some M hs x).1 x.2
  obtain ⟨a', b', he', hab'⟩ := (mem_R_some M hs y).1 y.2
  have hsum : g.e ((x + y : M.R) : E) = (((a + a' : 𝒪[F]) : F), ((b + b' : 𝒪[F]) : F)) := by
    rw [Subring.coe_add, map_add (f := _), he, he']; simp
  have hu := fst_isUnit M hs (x + y) hxy (a + a') (b + b') hsum
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h | h
  · exact hx (isUnit_of_fst M hOK hs x a b he hab h)
  · exact hy (isUnit_of_fst M hOK hs y a' b' he' hab' h)

end ModeG

theorem rFinMax_holds : RFinMax := by
  intro F _ _ _ E _ _ _ _ M hOK
  cases hs : M.split with
  | none =>
    exact finite_max_of_equiv (RingEquiv.subringCongr (PI.NGStepBBW.R_eq_O_of_none hs)) (finite_max_O M hOK)
  | some g =>
    haveI := isLocal_R M hOK hs
    refine (Set.finite_singleton (IsLocalRing.maximalIdeal M.R)).subset ?_
    intro m hm
    exact IsLocalRing.eq_maximalIdeal hm

theorem srLift_holds : SRLift := srLift_of_finMax rFinMax_holds

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents.RF
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnitCons
section
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

theorem E_strict {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) (i j : Fin (D.R.rS + 1)) (hji : j ≤ i) :
    (X - Psi w X⁻¹) i j = 0 := by
  have hP := Psi_upU w (upU_inv hU) (blk_inv w hU hB)
  rw [Matrix.sub_apply]
  rcases eq_or_lt_of_le hji with h | h
  · subst h; rw [(hU _ _).2 rfl, (hP _ _).2 rfl, sub_self]
  · rw [(hU _ _).1 h, (hP _ _).1 h, sub_self]

theorem unitCons (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ q, Agree δ M q) {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) (hG : GrD X)
    {a c : Fin (D.R.rS + 1)} (hac : a < c)
    (hlow : ∀ i j : Fin (D.R.rS + 1), i < j → j.val - i.val < c.val - a.val →
      (X - Psi w X⁻¹) i j ∈ qdPow D (j.val - i.val)) :
    Psi w (X - Psi w X⁻¹) a c - (X - Psi w X⁻¹) a c ∈ qdPow D (c.val - a.val) := by
  have hXd : IsUnit X.det := by rw [upU_det hU]; exact isUnit_one
  have hXi := upU_inv hU
  have hBi := blk_inv w hU hB
  have hGi := grD_inv hU hG
  have hY := Psi_upU w hU hB
  have hGY := Psi_grD w δ M hA hB hG
  have hPi : Psi w X⁻¹ = (Psi w X)⁻¹ := Psi_inv w hXd
  have hYd : IsUnit (Psi w X).det := by rw [upU_det hY]; exact isUnit_one
  have hES := E_strict w hU hB
  have hPE : Psi w (X - Psi w X⁻¹) = Psi w X * (X - Psi w X⁻¹) * X⁻¹ := by
    rw [Psi_sub, Psi_Psi w hBi, hPi, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hXd,
      Matrix.mul_nonsing_inv _ hYd, Matrix.one_mul]
  have decomp : Psi w X * (X - Psi w X⁻¹) * X⁻¹ - (X - Psi w X⁻¹) =
      (Psi w X - 1) * (X - Psi w X⁻¹) * X⁻¹ + (X - Psi w X⁻¹) * (X⁻¹ - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]; abel
  rw [hPE, ← Matrix.sub_apply, decomp, Matrix.add_apply]
  have hac' : a.val < c.val := hac
  refine (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem ?_ ?_
  · rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases h1 : a < i
    · have h1' : a.val < i.val := h1
      by_cases h2 : i < j
      · have h2' : i.val < j.val := h2
        by_cases h3 : j ≤ c
        · have h3' : j.val ≤ c.val := h3
          rw [show (Psi w X - 1) a i = Psi w X a i by rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt h1), sub_zero]]
          have m1 := hGY a i (le_of_lt h1)
          have m2 := hlow i j h2 (by omega)
          have m3 := hGi j c h3
          have := mem_qdPow_mul (mem_ddPow_mul_qd m1 m2) m3
          rwa [show i.val - a.val + (j.val - i.val) + (c.val - j.val) = c.val - a.val by omega] at this
        · rw [(hXi j c).1 (lt_of_not_ge h3), mul_zero]; exact FractionalIdeal.zero_mem _
      · rw [hES i j (not_lt.1 h2), mul_zero, zero_mul]; exact FractionalIdeal.zero_mem _
    · have h0 : (Psi w X - 1) a i = 0 := by
        rw [Matrix.sub_apply]
        rcases eq_or_lt_of_le (not_lt.1 h1) with h | h
        · rw [h, (hY _ _).2 rfl, Matrix.one_apply_eq, sub_self]
        · rw [(hY _ _).1 h, Matrix.one_apply_ne (ne_of_gt h), sub_self]
      rw [h0, zero_mul, zero_mul]; exact FractionalIdeal.zero_mem _
  · rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases h1 : a < j
    · have h1' : a.val < j.val := h1
      by_cases h2 : j < c
      · have h2' : j.val < c.val := h2
        rw [show (X⁻¹ - 1) j c = X⁻¹ j c by rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt h2), sub_zero]]
        have := mem_qdPow_mul (hlow a j h1 (by omega)) (hGi j c (le_of_lt h2))
        rwa [show j.val - a.val + (c.val - j.val) = c.val - a.val by omega] at this
      · have h0 : (X⁻¹ - 1) j c = 0 := by
          rw [Matrix.sub_apply]
          rcases eq_or_lt_of_le (not_lt.1 h2) with h | h
          · rw [h, (hXi _ _).2 rfl, Matrix.one_apply_eq, sub_self]
          · rw [(hXi _ _).1 h, Matrix.one_apply_ne (ne_of_gt h), sub_self]
        rw [h0, mul_zero]; exact FractionalIdeal.zero_mem _
    · rw [hES a j (not_lt.1 h1), zero_mul]; exact FractionalIdeal.zero_mem _

end Formalism.L2.SG.Pf.StabIntLat
end
end

