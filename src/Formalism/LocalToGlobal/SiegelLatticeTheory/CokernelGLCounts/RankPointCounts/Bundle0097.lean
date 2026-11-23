module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0095
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BlockRetr
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0092
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0091
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0048
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrbitCountSecondStage
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0005

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SameCell
section
noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

section Sg

variable {K : Type*} [Field K] {r : ℕ}

def Sg (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K := Matrix.diagonal fun b => (-1) ^ (r - b.val)

theorem Sg_mul_Sg : (Sg r : Matrix (Fin (r + 1)) (Fin (r + 1)) K) * Sg r = 1 := by
  rw [Sg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem zhatOM_eq (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ZhatOM Z = Z * Sg r := by
  ext a b
  rw [Sg, Matrix.mul_diagonal]
  show (-1) ^ (r - b.val) * Z a b = _
  ring

theorem upUni_Sg {U : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni U) : IsUpUni (Sg r * U * Sg r) := by
  intro i j
  simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun hji => by rw [(h i j).1 hji]; ring, fun hij => ?_⟩
  subst hij
  rw [(h i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]
  simp

end Sg

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem same_cell (F : FlagG S r T) (F1 F2 : FlagG S r T') (hG1 : Gflag F F1 ≠ 0) (hG2 : Gflag F F2 ≠ 0)
    (w : Point E (r + 1)) (h1 : IsInCell (ZhatOM (Zhat F F1)) w) (h2 : IsInCell (ZhatOM (Zhat F F2)) w) :
    ∃ g : S.V ≃ₗ[E] S.V, g ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧
      (∃ M : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni M ∧ ∀ b, g.symm (F.fvec b) = ∑ c, M c b • F.fvec c) ∧
      ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni U ∧ ∀ b, g (∑ c, U c b • F1.fvec c) = F2.fvec b := by
  obtain ⟨L1, U1, hL1, hU1, e1⟩ := h1
  obtain ⟨L2, U2, hL2, hU2, e2⟩ := h2
  rw [zhatOM_eq] at e1 e2
  have hL1d : IsUnit L1.det := by rw [loUni_det hL1]; exact isUnit_one
  have hU1d : IsUnit U1.det := by rw [upUni_det hU1]; exact isUnit_one
  set L := L2 * L1⁻¹ with hL
  set U := Sg r * (U1⁻¹ * U2) * Sg r with hU
  have hLl : IsLoUni L := loUni_mul hL2 (loUni_inv hL1)
  have hUu : IsUpUni U := upUni_Sg (upUni_mul (upUni_inv hU1) hU2)
  have hZ : Zhat F F2 = L * Zhat F F1 * U := by
    have z1 : Zhat F F1 = L1 * ptMat w * U1 * Sg r := by
      rw [← e1, Matrix.mul_assoc, Sg_mul_Sg, Matrix.mul_one]
    have z2 : Zhat F F2 = L2 * ptMat w * U2 * Sg r := by
      rw [← e2, Matrix.mul_assoc, Sg_mul_Sg, Matrix.mul_one]
    rw [z2, z1, hL, hU]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Sg r) (Sg r), Sg_mul_Sg, Matrix.one_mul, ← Matrix.mul_assoc U1 U1⁻¹,
      Matrix.mul_nonsing_inv _ hU1d, Matrix.one_mul, ← Matrix.mul_assoc L1⁻¹ L1,
      Matrix.nonsing_inv_mul _ hL1d, Matrix.one_mul]
  set M := Lᴴ with hM
  have hMu : IsUpUni M := loUni_iff_ct.1 hLl
  have hZ' : Zhat F F2 = Mᴴ * Zhat F F1 * U := by rw [hM, conjTranspose_conjTranspose]; exact hZ
  obtain ⟨g, hg, hgx⟩ := witt_tuple (tupMU F F1 M U) (Sum.elim F.fvec F2.fvec) (tupMU_indep F F1 M U hMu hUu hG1)
    (PI.PairCorankPos.W.linIndep F F2 hG2) (gram_moved F F1 F2 M U hMu hUu hZ')
  refine ⟨g, hg, ⟨M, hMu, fun b => ?_⟩, U, hUu, fun b => hgx (Sum.inr b)⟩
  have := hgx (Sum.inl b)
  simp only [tupMU, Sum.elim_inl] at this
  rw [← this, LinearEquiv.symm_apply_apply]

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TauTau
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.ProdEP2Core

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)

def sgnU : GLp p :=
  ⟨Formalism.L2.SG.LsDatumB.sgnP p, Formalism.L2.SG.LsDatumB.sgnP p, Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p,
    Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p⟩

def tau : GG p →* GG p where
  toFun x := (x.1, MulOpposite.op (sgnU p * x.2.unop * sgnU p))
  map_one' := by
    have hs : sgnU p * sgnU p = 1 := Units.ext (Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p)
    ext1
    · rfl
    · apply MulOpposite.unop_injective
      show sgnU p * (1 : GLp p) * sgnU p = 1
      rw [mul_one, hs]
  map_mul' x y := by
    have hs : sgnU p * sgnU p = 1 := Units.ext (Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p)
    ext1
    · rfl
    · apply MulOpposite.unop_injective
      simp only [Prod.snd_mul, MulOpposite.unop_mul, MulOpposite.unop_op]
      calc sgnU p * (y.2.unop * x.2.unop) * sgnU p
          = sgnU p * y.2.unop * (sgnU p * sgnU p) * x.2.unop * sgnU p := by rw [hs]; group
        _ = _ := by group

theorem tau_tau (x : GG p) : tau p (tau p x) = x := by
  have hs : sgnU p * sgnU p = 1 := Units.ext (Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p)
  ext1
  · rfl
  · apply MulOpposite.unop_injective
    show sgnU p * (sgnU p * x.2.unop * sgnU p) * sgnU p = x.2.unop
    calc sgnU p * (sgnU p * x.2.unop * sgnU p) * sgnU p = (sgnU p * sgnU p) * x.2.unop * (sgnU p * sgnU p) := by
          group
      _ = _ := by rw [hs]; group

end Formalism.L2.SG.Pf.CountAt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolFin
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolFin

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal PI.UnitaryGroupMassFormula.CntFormula
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem reps (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : RowsOf u F0 what₂) (Z : MatZ D)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) :
    ∃ K : Set ((Fin D.R.rS → (VS D).V) × (VS D).V), K.Finite ∧
      ∀ F' ∈ EZ (Tn u') F0 Λ Z, ∃ n ∈ N0 F0 Λ, ((fun a => n (F'.fl.e a)), n F'.fl.z) ∈ K := by
  by_cases hne : (EZ (Tn u') F0 Λ Z).Nonempty
  · obtain ⟨F₁, hF₁⟩ := hne
    simp only [EZ, Set.mem_ofPred_eq] at hF₁
    have hG := hF₁.1.2.2
    rw [gz_eq, hF₁.2.2.2.2] at hG
    obtain ⟨R, hR1⟩ := rank_gram D _ _ Z hG
    have hfix := fixedOK_of_rows D u F0 what₂ hR hΛ
    obtain ⟨Wf, hWf, hW⟩ := orbit_count_first_stage D (Tn u') F0 Λ hfix Z R hR1
    obtain ⟨Af, hAf, hA⟩ := orbit_count_second_stage D (Tn u') F0 Λ hfix Z R hR1 Wf hWf
    refine ⟨_, finite_level_index D (Tn u') F0 Λ hfix Z R hR1 Wf Af hWf hAf, ?_⟩
    intro F' hF'
    have hx := good_places_integral D (Tn u') F0 Λ Z F' hF'
    obtain ⟨n₁, hn₁, h₁⟩ := hW _ hx
    have hx₁ := good_move D (Tn u') F0 Λ Z hx hn₁
    obtain ⟨n₂, hn₂, h₂, h₃⟩ := hA _ hx₁ h₁
    refine ⟨n₁.trans n₂, (unipotent_integral_isGroup D F0 Λ).2.2 n₁ hn₁ n₂ hn₂, ?_⟩
    refine ⟨good_move D (Tn u') F0 Λ Z hx₁ hn₂, ?_, h₃⟩
    have h₄ : pWf D (act D n₂ (act D n₁ (F'.fl.e, F'.fl.z))) ∈ Wf := h₂ ▸ h₁
    exact h₄
  · exact ⟨∅, Set.finite_empty, fun F' hF' => (hne ⟨F', hF'⟩).elim⟩

theorem fin0 (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : RowsOf u F0 what₂) (Z : MatZ D)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) : cntE (Tn u') F0 Λ Z ≠ ⊤ := by
  obtain ⟨K, hK, hKrep⟩ := reps D u u' F0 what₂ hR Z Λ hΛ
  have hgrp := unipotent_integral_isGroup D F0 Λ
  let g : ((Fin D.R.rS → (VS D).V) × (VS D).V) → Set (LFlag (VS D) D.R.rS (Tn u')) :=
    fun k => {F'' | F'' ∈ EZ (Tn u') F0 Λ Z ∧
      ∃ n ∈ N0 F0 Λ, ((fun a => n (F''.fl.e a)), n F''.fl.z) = k}
  have hsub : {O | ∃ F' ∈ EZ (Tn u') F0 Λ Z,
      O = {F'' | F'' ∈ EZ (Tn u') F0 Λ Z ∧ NilradicalFlagMoved F0 Λ F' F''}} ⊆ g '' K := by
    rintro O ⟨F', hF', rfl⟩
    obtain ⟨n, hn, hk⟩ := hKrep F' hF'
    refine ⟨_, hk, ?_⟩
    ext F''
    simp only [g, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hF'', m, hm, hme⟩
      refine ⟨hF'', n.trans m.symm, hgrp.2.2 n hn _ (hgrp.2.1 m hm), fun a => ?_, ?_⟩
      · have h := congrFun (congrArg Prod.fst hme) a
        simp only at h
        simp [← h]
      · have h := congrArg Prod.snd hme
        simp only at h
        simp [← h]
    · rintro ⟨hF'', m, hm, he, hz⟩
      refine ⟨hF'', m.symm.trans n, hgrp.2.2 _ (hgrp.2.1 m hm) n hn, ?_⟩
      ext a <;> simp [← he, ← hz]
  simp only [cntE]
  exact ((hK.image g).subset hsub).encard_lt_top.ne

theorem finR (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : IsRowReps D F0 what₂) (Z : MatZ D)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) : cntE (Tn u') F0 Λ Z ≠ ⊤ := by
  obtain ⟨F1, he1, hz1⟩ := Formalism.MainNotions.S.Inh.tie_flagG_nonempty D u
  have hT : Tn u ≠ 0 := by exact_mod_cast (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u).ne'
  obtain ⟨β, hβ, hβe, hβz⟩ := Formalism.L2.SG.Pf.WittFlags.flag_witt hT rfl F0 F1
  have hrows := Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D β hβ F0 what₂ hR
  have hmem : Formalism.HermitianLatticesTheory.gmap β Λ ∈ what₂.image (Formalism.HermitianLatticesTheory.gmap β) := Finset.mem_image_of_mem _ hΛ
  have hRo : RowsOf u (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (what₂.image (Formalism.HermitianLatticesTheory.gmap β)) := by
    refine ⟨?_, ?_, hrows, ⟨_, hmem⟩⟩
    · rw [← he1]
      funext a
      exact hβe a
    · rw [← hz1]
      exact hβz
  have h := fin0 D u u' _ _ hRo Z _ hmem
  rwa [Formalism.L2.SG.Pf.Cnt.counting_iso_inverse D β hβ (Tn u') F0 Λ Z] at h

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem orbitFinite_holds : Formalism.L2.SG.Pf.ZsVolOrb.OrbFinE M δ u u' F0 what₂ := by
  intro γ w F' L U hH
  have hfin := finR D u u' F0 what₂ hH.2.2.1 (ZhatL (lf D F0) F') γ.lam γ.mem
  unfold cntE at hfin
  refine (Set.encard_ne_top_iff.mp hfin).subset ?_
  rintro O ⟨F'', hF'', _, rfl⟩
  exact ⟨F'', hF'', rfl⟩

end Formalism.L2.SG.Pf.ZsVolFin

end
end

