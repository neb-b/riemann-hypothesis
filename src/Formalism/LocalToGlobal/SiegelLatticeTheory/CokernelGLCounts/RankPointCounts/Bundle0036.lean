module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumGlue
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0032
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0031

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumTop
section
noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbSumPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB

variable {D : Formalism.BasicNotions.D7}

theorem orbCut_all {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) : OrbCut M a c := by
  haveI := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK M hOK
  exact Formalism.L2.SG.Pf.LocOrbCut.orbitDecomposition_of_integrand M hOK a c (Formalism.L2.SG.Pf.LocOrbCut.val M hOK a c)

theorem localOrbitSum_holds (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (hA : ∀ p, Agree δ M p) :
    LocOrbSum M δ u u' :=
  locOrbSum_of M δ u u' (fun p w => modShift_holds δ _ _ p w)
    (fun p a c => orbCut_all (M p) (hA p).1 a c)
    (fun p => nAutNe_of M p (hA p).1)

end Formalism.L2.SG.Pf.LocOrbSumPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocRealAtOrd
section
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.PCountEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Assembly

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

def LocRealAt (p : PlF D) : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)), IsLCls M δ (D.mem u).A.T (D.mem u').A.T p w O →
    ∃ (Lp Up : MatP D p) (c : 𝓞 D.host.F), c ≠ 0 ∧ IsLo Lp ∧ IsUp Up ∧
      ∀ L U : PairVal.MatR D, IsLo L → IsUp U →
        (∀ a b, ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (L a b) - Lp a b =
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) * o) →
        (∀ a b, ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (U a b) - Up a b =
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) * o) →
        tupZ M δ u u' (L * ptMat w * U * Sg D.host.E D.R.rS) p = O

variable {M δ}

theorem locRealAt_ord (hA : ∀ p, Agree δ M p) (p : PlF D) (hM : (M p).split = none) : LocRealAt M δ u u' p :=
  fun w O hO => locReal_ord hA u u' w p hM O hO

theorem adj_mem {R : Type*} [CommRing R] (S : Subring R) {n : ℕ} {l : Matrix (Fin n) (Fin n) R}
    (hl : ∀ a b, l a b ∈ S) (a b : Fin n) : l.adjugate a b ∈ S := by
  let lR : Matrix (Fin n) (Fin n) S := fun a b => ⟨l a b, hl a b⟩
  have h1 : lR.map S.subtype = l := by ext a b; rfl
  have h2 := congrFun (congrFun (RingHom.map_adjugate S.subtype lR) a) b
  rw [← h1, show lR.map S.subtype = S.subtype.mapMatrix lR from rfl, ← h2]
  exact (lR.adjugate a b).2

theorem congr_dvd {p : PlF D} {y : (D.s.atP p).Ep} {c c' r : 𝓞 D.host.F} (hc : c = c' * r)
    (h : ∃ o ∈ (D.s.atP p).O, y =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) * o) :
    ∃ o ∈ (D.s.atP p).O, y =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c')) * o := by
  obtain ⟨o, ho, rfl⟩ := h
  refine ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F r)) * o,
    Subring.mul_mem _ (alg_mem_O (fun q => D.s.atP q) p (iotaF_int_mem (fun q => D.s.atP q) p r)) ho, ?_⟩
  rw [hc, map_mul, map_mul, map_mul, mul_assoc]

theorem exist_of (hA : ∀ p, Agree δ M p) (hTy : ∀ p, (M p).split ≠ none → LocRealAt M δ u u' p) :
    Exist M δ u u' := by
  intro w' _ x hx
  have hLR : ∀ p, LocRealAt M δ u u' p := fun p => by
    by_cases h : (M p).split = none
    · exact locRealAt_ord u u' hA p h
    · exact hTy p h
  have hloc := fun p => hLR p w' (x.1 p) (hx p)
  choose Lp Up cp hcp0 hLp hUp hreal using hloc
  have hgood := Formalism.L2.SG.Pf.LocModel.good_cofinite δ M hA ∅
  have hBad := Filter.eventually_cofinite.1 hgood
  set S : Finset (PlF D) := x.2.toFinset ∪ hBad.toFinset with hS
  set c : 𝓞 D.host.F := ∏ p ∈ S, cp p with hcdef
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hcp0 p
  obtain ⟨L, hL1, hL0, hLS, hLO⟩ := approx_lo (fun q => D.s.atP q) S c hc0 (fun p => Lp p)
    (fun p _ a => (hLp p).1 a) (fun p _ a b hab => (hLp p).2 a b hab)
  obtain ⟨U, hU1, hU0, hUS, hUO⟩ := approx_up (fun q => D.s.atP q) S c hc0 (fun p => Up p)
    (fun p _ a => (hUp p).1 a) (fun p _ a b hab => (hUp p).2 b a hab)
  have hLlo : IsLo L := ⟨hL1, hL0⟩
  have hUup : IsUp U := ⟨hU1, fun a b hab => hU0 b a hab⟩
  have hZ : (L * ptMat w' * U * Sg D.host.E D.R.rS) * Sg D.host.E D.R.rS = L * ptMat w' * U := by
    rw [Matrix.mul_assoc, sg_sq, Matrix.mul_one]
  refine ⟨L * ptMat w' * U * Sg D.host.E D.R.rS, ⟨L, U, fun i j => ⟨hL0 i j, fun h => h ▸ hL1 i⟩,
    fun i j => ⟨hU0 i j, fun h => h ▸ hU1 i⟩, by rw [zhatOM_eq]; exact hZ⟩, ?_⟩
  funext p
  by_cases hp : p ∈ S
  · have hsplit : c = cp p * ∏ q ∈ S.erase p, cp q := (Finset.mul_prod_erase S cp hp).symm
    exact hreal p L U hLlo hUup (fun a b => congr_dvd hsplit (hLS p hp a b))
      (fun a b => congr_dvd hsplit (hUS p hp a b))
  · have hpx : x.1 p = x0L M δ (D.mem u).A.T (D.mem u').A.T p w' := by
      by_contra h
      exact hp (Finset.mem_union_left _ (x.2.mem_toFinset.2 h))
    have hpg : (M p).split = none ∧ (δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) ∧
        ((D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧
          (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O) ∧
        ∀ t ∈ (∅ : Finset D.host.E), ∀ k : Fin 3, t + ((k : ℕ) : D.host.E) ≠ 0 →
          (D.s.atP p).ιE (t + ((k : ℕ) : D.host.E)) ∈ (D.s.atP p).O ∧
            (D.s.atP p).ιE ((t + ((k : ℕ) : D.host.E))⁻¹) ∈ (D.s.atP p).O := by
      by_contra h
      exact hp (Finset.mem_union_right _ (hBad.mem_toFinset.2 h))
    have hentL : ∀ a b, (D.s.atP p).ιE (L a b) ∈ (D.s.atP p).O := hLO p hp
    have hentU : ∀ a b, (D.s.atP p).ιE (U a b) ∈ (D.s.atP p).O := hUO p hp
    have hLd : L.det = 1 := det_lo' hLlo
    have hUd : U.det = 1 := det_up' hUup
    have hinv : ∀ (X : PairVal.MatR D), X.det = 1 → (∀ a b, (D.s.atP p).ιE (X a b) ∈ (D.s.atP p).O) →
        ∀ a b, (D.s.atP p).ιE (X⁻¹ a b) ∈ (D.s.atP p).O := by
      intro X hX hXe a b
      rw [Matrix.inv_def, hX, Ring.inverse_one, one_smul]
      have h2 := congrFun (congrFun (RingHom.map_adjugate (D.s.atP p).ιE X) a) b
      rw [show ((D.s.atP p).ιE.mapMatrix X.adjugate) a b = (D.s.atP p).ιE (X.adjugate a b) from rfl] at h2
      rw [h2]
      exact adj_mem (D.s.atP p).O (fun a b => hXe a b) a b
    rw [hpx]
    exact tupZ_eq_x0L_at hA u u' hLlo hUup hZ p hpg.1 hpg.2.1.1 hpg.2.1.2 hpg.2.2.1.1 hpg.2.2.1.2
      (fun a b => ⟨hentL a b, hentU a b, hinv L hLd hentL a b, hinv U hUd hentU a b⟩)

end Assembly

end Formalism.L2.SG.Pf.PCountEx
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumATop
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Top

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem glue_at (M : Model F E) (r n : ℕ) (hM : M.OK) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hG : GramMM M r n) (hFG : ThFG M r) (hS : ThSpan M r) : Glue M r n :=
  glue_of M r n (glueFwd_of M r n hM (corrIso_holds M r n) hE)
    (glueBack_of M r n hM (corrIso_holds M r n) hE hV hP hG hFG hS) (glueInj_of M r n hM (corrIso_holds M r n))

theorem latSide_at (M : Model F E) (r n : ℕ) (hM : M.OK) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hG : GramMM M r n) (hFG : ThFG M r) (hS : ThSpan M r) (hR : ClaimR M r n) :
    LatSide M r n :=
  latSide_of M r n (glue_at M r n hM hE hV hP hG hFG hS) hR

end Top

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MapInvMul
section
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount

section Comp

variable {E : Type*} [Field E] {K : Type*} [CommRing K] (ψ : E →+* K) {r : ℕ}

def cP (cv : Fin (r + 1) → K) (L₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal cv * L₁.map ψ

def cP' (cv' : Fin (r + 1) → K) (L₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  L₁⁻¹.map ψ * Matrix.diagonal cv'

def cQ (cv : Fin (r + 1) → K) (U₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  U₁.map ψ * Matrix.diagonal cv

def cQ' (cv' : Fin (r + 1) → K) (U₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal cv' * U₁⁻¹.map ψ

theorem diag_one {cv cv' : Fin (r + 1) → K} (h : ∀ a, cv a * cv' a = 1) :
    Matrix.diagonal cv * Matrix.diagonal cv' = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  exact congrArg Matrix.diagonal (funext h)

theorem map_one' : (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E).map ψ = 1 := Matrix.map_one _ ψ.map_zero ψ.map_one

theorem map_inv_mul {L : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : L.det = 1) : L⁻¹.map ψ * L.map ψ = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (by rw [h]; exact isUnit_one), map_one']

theorem map_mul_inv {L : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : L.det = 1) : L.map ψ * L⁻¹.map ψ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (by rw [h]; exact isUnit_one), map_one']

theorem mono_map (σ : Fin (r + 1) → Fin (r + 1)) (ν : Fin (r + 1) → E) :
    (mono σ ν).map ψ = mono σ (fun a => ψ (ν a)) := by
  ext a b
  simp only [Matrix.map_apply, mono, Matrix.of_apply]
  split_ifs <;> simp

theorem inv_eq_map {x : E} (hx : x ≠ 0) : Ring.inverse (ψ x) = ψ x⁻¹ := by
  have h1 : ψ x * ψ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  calc Ring.inverse (ψ x) = Ring.inverse (ψ x) * (ψ x * ψ x⁻¹) := by rw [h1, mul_one]
    _ = ψ x⁻¹ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ ⟨⟨ψ x, ψ x⁻¹, h1, by rw [mul_comm]; exact h1⟩, rfl⟩, one_mul]

theorem hcv'_of {cv cv' : Fin (r + 1) → K} (hcv : ∀ a, cv a * cv' a = 1) : ∀ a, cv' a * cv a = 1 :=
  fun a => by rw [mul_comm]; exact hcv a

variable {cv cv' : Fin (r + 1) → K} (hcv : ∀ a, cv a * cv' a = 1) {L₁ U₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
include hcv hL₁ hU₁

theorem conjPrime_conjPrime₂ : cP ψ cv L₁ * cP' ψ cv' L₁ = 1 := by
  unfold cP cP'
  rw [show Matrix.diagonal cv * L₁.map ψ * (L₁⁻¹.map ψ * Matrix.diagonal cv') =
      Matrix.diagonal cv * (L₁.map ψ * L₁⁻¹.map ψ) * Matrix.diagonal cv' by simp only [Matrix.mul_assoc],
    map_mul_inv ψ (det_lo hL₁), Matrix.mul_one, diag_one hcv]

theorem cP'_cP : cP' ψ cv' L₁ * cP ψ cv L₁ = 1 := by
  unfold cP cP'
  rw [show L₁⁻¹.map ψ * Matrix.diagonal cv' * (Matrix.diagonal cv * L₁.map ψ) =
      L₁⁻¹.map ψ * (Matrix.diagonal cv' * Matrix.diagonal cv) * L₁.map ψ by simp only [Matrix.mul_assoc],
    diag_one (hcv'_of hcv), Matrix.mul_one, map_inv_mul ψ (det_lo hL₁)]

theorem cQ_cQ' : cQ ψ cv U₁ * cQ' ψ cv' U₁ = 1 := by
  unfold cQ cQ'
  rw [show U₁.map ψ * Matrix.diagonal cv * (Matrix.diagonal cv' * U₁⁻¹.map ψ) =
      U₁.map ψ * (Matrix.diagonal cv * Matrix.diagonal cv') * U₁⁻¹.map ψ by simp only [Matrix.mul_assoc],
    diag_one hcv, Matrix.mul_one, map_mul_inv ψ (det_up hU₁)]

theorem cQ'_cQ : cQ' ψ cv' U₁ * cQ ψ cv U₁ = 1 := by
  unfold cQ cQ'
  rw [show Matrix.diagonal cv' * U₁⁻¹.map ψ * (U₁.map ψ * Matrix.diagonal cv) =
      Matrix.diagonal cv' * (U₁⁻¹.map ψ * U₁.map ψ) * Matrix.diagonal cv by simp only [Matrix.mul_assoc],
    map_inv_mul ψ (det_up hU₁), Matrix.mul_one, diag_one (hcv'_of hcv)]

theorem cP_lo {k : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hk : IsLo k) : IsLo (cP' ψ cv' L₁ * k * cP ψ cv L₁) := by
  unfold cP cP'
  rw [show L₁⁻¹.map ψ * Matrix.diagonal cv' * k * (Matrix.diagonal cv * L₁.map ψ) =
      L₁⁻¹.map ψ * (Matrix.diagonal cv' * k * Matrix.diagonal cv) * L₁.map ψ by simp only [Matrix.mul_assoc]]
  exact isLo_mul (isLo_mul (isLo_map ψ (isLo_inv hL₁)) (isLo_conj hk cv' cv (hcv'_of hcv))) (isLo_map ψ hL₁)

theorem cQ_up {k : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hk : IsUp k) : IsUp (cQ ψ cv U₁ * k * cQ' ψ cv' U₁) := by
  unfold cQ cQ'
  rw [show U₁.map ψ * Matrix.diagonal cv * k * (Matrix.diagonal cv' * U₁⁻¹.map ψ) =
      U₁.map ψ * (Matrix.diagonal cv * k * Matrix.diagonal cv') * U₁⁻¹.map ψ by simp only [Matrix.mul_assoc]]
  exact isUp_mul (isUp_mul (isUp_map ψ hU₁) (isUp_conj hk cv cv' hcv)) (isUp_map ψ (isUp_inv hU₁))

theorem cW_eq (σ : Fin (r + 1) → Fin (r + 1)) (ν : Fin (r + 1) → E) (s e : K) :
    s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r =
      s • (cP ψ cv L₁ * mono σ (fun a => ψ (ν a)) * cQ ψ cv U₁) - e • Ecorner r := by
  unfold cP cQ
  rw [Matrix.map_mul, Matrix.map_mul, mono_map]
  simp only [Matrix.mul_assoc]

theorem cG_eq (X' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    cP' ψ cv' L₁ * (Matrix.diagonal cv * (L₁ * X' * L₁⁻¹).map ψ * Matrix.diagonal cv') * cP ψ cv L₁ = X'.map ψ := by
  have e : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Matrix.diagonal cv' * (Matrix.diagonal cv * M) = M :=
    fun M => by rw [← Matrix.mul_assoc, diag_one (hcv'_of hcv), Matrix.one_mul]
  have f : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) K, L₁⁻¹.map ψ * (L₁.map ψ * M) = M :=
    fun M => by rw [← Matrix.mul_assoc, map_inv_mul ψ (det_lo hL₁), Matrix.one_mul]
  unfold cP cP'
  rw [Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc, e, f, map_inv_mul ψ (det_lo hL₁), Matrix.mul_one]

theorem conj_mul {P P' A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hPP : P * P' = 1) :
    P' * (A * B) * P = (P' * A * P) * (P' * B * P) := by
  rw [show P' * A * P * (P' * B * P) = P' * A * (P * P') * B * P by simp only [Matrix.mul_assoc], hPP,
    Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem comp_target {σ : Fin (r + 1) → Fin (r + 1)} (hσ : ∀ a, σ (σ a) = a) {ν : Fin (r + 1) → E}
    (hν : ∀ a, ν a ≠ 0) {s e : K} (hs : IsUnit s) {kL kR : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hkL : IsLo kL)
    (hkR : IsUp kR)
    (hk : kL * (s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) * kR =
      s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) :
    IsLo (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹ ∧ (∀ i j, σ j < σ i → (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹ i j = 0) ∧
      (cP' ψ cv' L₁ * kL * cP ψ cv L₁) * (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹ = 1 := by
  have hν' : ∀ x, IsUnit (ψ (ν x)) := fun x => by
    have hu : ψ (ν x) * ψ (ν x)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ (hν x), map_one]
    exact ⟨⟨ψ (ν x), ψ (ν x)⁻¹, hu, by rw [mul_comm, hu]⟩, rfl⟩
  rw [cW_eq ψ hcv hL₁ hU₁] at hk
  have hfix := stab_core hs (cP'_cP ψ hcv hL₁ hU₁) (cQ_cQ' ψ hcv hL₁ hU₁) hkL hkR hk
  exact fix_inv hσ hν' (cP_lo ψ hcv hL₁ hU₁ hkL) (cQ_up ψ hcv hL₁ hU₁ hkR) hfix

theorem comp_main {σ : Fin (r + 1) → Fin (r + 1)} (hσ : ∀ a, σ (σ a) = a) {ν : Fin (r + 1) → E}
    (hν : ∀ a, ν a ≠ 0) {s e : K} (hs : IsUnit s) {I : Subring K} {kL kR a b : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hkL : IsLo kL) (hkR : IsUp kR)
    (hk : kL * (s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) * kR =
      s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r)
    (ha : IsLo a) (hb : IsUp b)
    (hab : a * (s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) * b =
      s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r)
    {X' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (haX : a = kL * (Matrix.diagonal cv * (L₁ * X' * L₁⁻¹).map ψ * Matrix.diagonal cv'))
    {t c : K} (ht : t ∈ I) (hc : c ∈ I) (hbν : ∀ a, t * ψ (ν a) ∈ I) (hbν' : ∀ a, t * ψ (ν a)⁻¹ ∈ I)
    (bP : ∀ i j, t * cP ψ cv L₁ i j ∈ I) (bP' : ∀ i j, t * cP' ψ cv' L₁ i j ∈ I)
    (bQ : ∀ i j, t * cQ ψ cv U₁ i j ∈ I) (bQ' : ∀ i j, t * cQ' ψ cv' U₁ i j ∈ I)
    (bx : ∀ i j, t * (cP' ψ cv' L₁ * kL * cP ψ cv L₁) i j ∈ I)
    (hG : EntIn (lat I (t * (t * (t * (t * (t * c)))))) (X'.map ψ - (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹)) :
    EntIn (lat I c) (a - 1) ∧ EntIn (lat I c) (b - 1) := by
  have hν' : ∀ x, IsUnit (ψ (ν x)) := fun x => by
    have hu : ψ (ν x) * ψ (ν x)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ (hν x), map_one]
    exact ⟨⟨ψ (ν x), ψ (ν x)⁻¹, hu, by rw [mul_comm, hu]⟩, rfl⟩
  have hinv : ∀ x, t * Ring.inverse (ψ (ν x)) ∈ I := fun x => by
    rw [inv_eq_map ψ (hν x)]
    exact hbν' x
  have hT := (comp_target ψ hcv hL₁ hU₁ hσ hν hs hkL hkR hk).2.2
  have hA : cP' ψ cv' L₁ * a * cP ψ cv L₁ = (cP' ψ cv' L₁ * kL * cP ψ cv L₁) * X'.map ψ := by
    rw [haX, conj_mul hcv hL₁ hU₁ (conjPrime_conjPrime₂ ψ hcv hL₁ hU₁), cG_eq ψ hcv hL₁ hU₁]
  have hE := close_of_target hT bx hG
  rw [← hA] at hE
  rw [cW_eq ψ hcv hL₁ hU₁] at hab
  exact close_pair hσ hν' ht hc hbν hinv (conjPrime_conjPrime₂ ψ hcv hL₁ hU₁) (cP'_cP ψ hcv hL₁ hU₁)
    (cQ_cQ' ψ hcv hL₁ hU₁) (cQ'_cQ ψ hcv hL₁ hU₁) bP bP' bQ bQ' hs ha hb hab (cP_lo ψ hcv hL₁ hU₁ ha)
    (cQ_up ψ hcv hL₁ hU₁ hb) hE

end Comp

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnipotentFrameFixers
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem equiv_of_corr {X L S : Type*} (P : X → Prop) (cl : X → S) (G : Set L) (R : X → L → Prop)
    (ha : ∀ x, P x → ∃ y ∈ G, R x y) (hb : ∀ y ∈ G, ∃ x, P x ∧ R x y)
    (hc : ∀ x x' y y', P x → P x' → R x y → R x' y' → (y = y' ↔ cl x = cl x')) :
    Nonempty ({O | ∃ x, P x ∧ O = cl x} ≃ G) := by
  refine ⟨{ toFun := fun O => ⟨(ha _ O.2.choose_spec.1).choose, (ha _ O.2.choose_spec.1).choose_spec.1⟩
            invFun := fun y => ⟨cl (hb y.1 y.2).choose, _, (hb y.1 y.2).choose_spec.1, rfl⟩
            left_inv := ?_
            right_inv := ?_ }⟩
  · rintro ⟨O, hO⟩
    apply Subtype.ext
    have h1 := (ha _ hO.choose_spec.1).choose_spec
    have h2 := (hb _ h1.1).choose_spec
    have h3 := (hc _ _ _ _ hO.choose_spec.1 h2.1 h1.2 h2.2).1 rfl
    show cl (hb _ h1.1).choose = O
    exact (hO.choose_spec.2.trans h3).symm
  · rintro ⟨y, hy⟩
    apply Subtype.ext
    have h2 := (hb y hy).choose_spec
    have hm : ∃ x, P x ∧ cl (hb y hy).choose = cl x := ⟨_, h2.1, rfl⟩
    have h4 := (ha _ hm.choose_spec.1).choose_spec
    show (ha _ hm.choose_spec.1).choose = y
    exact (hc _ _ _ _ hm.choose_spec.1 h2.1 h4.2 h2.2).2 hm.choose_spec.2.symm

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def unipotentFrameFixers {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) :=
  {n | n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ j, ∀ x ∈ Xflag (lf D F0) (j + 1), n x - x ∈ Xflag (lf D F0) j) ∧
    (∀ x ∈ orth (VS D) (Xsp (lf D F0)), n x - x ∈ Xsp (lf D F0)) ∧ (∀ a, n (F0.e a) = F0.e a) ∧ n F0.z = F0.z}

def Moves {T' : D.host.E} (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F' F'' : LFlag (D.sp.Y 0) D.R.rS T') : Prop :=
  (∀ a, n (F'.fl.e a) = F''.fl.e a) ∧ n F'.fl.z = F''.fl.z

def IsPartner (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Prop :=
  F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z ∧
    ∃ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' ∧
      Rep γ'.lam (lf D F0) (PD D γ'.lam (lf D F0) u') γ'.cls F'

def cls (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) :=
  {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z ∧ CntLocal.NilradicalFlagMoved F0 γ.lam F' F''}

theorem frPart_eq (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) :
    frPart γ Z = {O | ∃ F', IsPartner γ Z F' ∧ O = cls γ Z F'} := by
  ext O
  constructor
  · rintro ⟨F', h1, h2, h3⟩
    exact ⟨F', ⟨h1, h2⟩, h3⟩
  · rintro ⟨F', ⟨h1, h2⟩, h3⟩
    exact ⟨F', h1, h2, h3⟩

def RelN (γ : TermDef.Term D u u' F0 what₂) (F'₂ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) : Prop :=
  ∃ n ∈ unipotentFrameFixers F0, Moves n F'₂ F' ∧ (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)

def Ctx (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) : Prop :=
  ∃ w : Point D.host.E (D.R.rS + 1), EligAt γ w ∧ ∃ w' : Point D.host.E (D.R.rS + 1),
    Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 ∧ kind w' = kind w ∧ AtMat w' Z

def StarHyp (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)) : Prop :=
  ZhatL (lf D F0) F'₂ = Z ∧
    (∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (φ p) (φ' p)) ∧
    ∀ p, φ p = LinearEquiv.refl _ _

def Coherent (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)) : Prop :=
  ∃ Λ₀ : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsFullLattice D.host.E Λ₀ ∧
    {p | locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p) ≠ {lattice₂ D Zd.M p Λ₀}}.Finite

variable (u u' F0 what₂)

def StarExists2 : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∃ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' ∧ Coherent Zd γ F'₂ φ φ'

def FwdC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ F', IsPartner γ Z F' → ∃ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', RelN γ F'₂ F' Λ₂

def BwdC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', ∃ F', IsPartner γ Z F' ∧ RelN γ F'₂ F' Λ₂

def UniqC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ F' F'' Λ₂ Λ₃, IsPartner γ Z F' → IsPartner γ Z F'' → RelN γ F'₂ F' Λ₂ → RelN γ F'₂ F'' Λ₃ →
        (Λ₂ = Λ₃ ↔ cls γ Z F' = cls γ Z F'')

variable {u u' F0 what₂}

theorem fStarC_of_route2 (h1 : StarExists2 Zd u u' F0 what₂) (h2 : FwdC Zd u u' F0 what₂) (h3 : BwdC Zd u u' F0 what₂)
    (h4 : UniqC Zd u u' F0 what₂) : FStarC Zd u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ
  have hC : Ctx γ Z := ⟨w, hγ, w', hG', hk, hZ⟩
  obtain ⟨F'₂, φ, φ', hS, hCoh⟩ := h1 γ Z hC
  obtain ⟨Λ₀, hΛ₀, hfin⟩ := hCoh
  letI := hΛ₀
  refine ⟨F'₂, φ, φ', hS.1, hS.2.2, hS.2.1, ⟨Λ₀, inferInstance, hfin⟩, ?_⟩
  rw [frPart_eq]
  exact equiv_of_corr (IsPartner γ Z) (cls γ Z) (GlobSet Zd γ F'₂ φ φ') (RelN γ F'₂)
    (h2 γ Z hC F'₂ φ φ' hS) (h3 γ Z hC F'₂ φ φ' hS) (h4 γ Z hC F'₂ φ φ' hS)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

