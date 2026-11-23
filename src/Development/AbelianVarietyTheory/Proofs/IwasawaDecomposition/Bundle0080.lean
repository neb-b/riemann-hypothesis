module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0076
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockDataLevelFormsTransportFieldMap
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Formalism.LocalToGlobal.Divisibility.RowSideTie

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisEqAcrisLocalizationPeriodTStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_eq_acris_localization_periodT : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (b : Per.Bcris l), ∃ (r : ℕ) (x : Per.Acris l), b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ r = algebraMap (Per.Acris l) (Per.Bcris l) x := by
  first | exact @GlobalTheory.MemLoc.bcris_eq_acris_localization_periodT_alt | exact GlobalTheory.MemLoc.bcris_eq_acris_localization_periodT_alt | (intros; apply GlobalTheory.MemLoc.bcris_eq_acris_localization_periodT_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockDatumBaseChangeDefiniteLatticeCompatible
section
noncomputable section

namespace GlobalTheory.Mem.R3.LiftLatBC

open Module NumberField Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.Mem.R3.DefLatBC
open scoped Matrix

theorem tl_bcF_of_blockBCAt : ∀ {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}
  (φ : K →+* K'), (∀ x : K, φ (star x) = star (φ x)) → ∀ (e : G ≃* G') (B : Formalism.L2.DIV.BlockDat K G Pl0) (B' : Formalism.L2.DIV.BlockDat K' G' Pl0')
    (ℓ : Formalism.L2.DIV.Lvl K G) (ℓ' : Formalism.L2.DIV.Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (s : ℕ)
    (C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K'), B.Ok s → GlobalTheory.Mem.R3.LiftLatBC.BlockBaseChangeAt φ e B B' ℓ ℓ' Z Z' C →
    ∃ Gm : Matrix (Fin (B'.dZ ℓ' Z')) (Fin (B.dZ ℓ Z)) K', Function.Bijective Gm.mulVec ∧
      B'.Tl ℓ' Z' = Submodule.span (𝓞 K') ((fun x : Fin (B.dZ ℓ Z) → K => Matrix.mulVec Gm (fun k => φ (x k))) '' (B.Tl ℓ Z : Set (Fin (B.dZ ℓ Z) → K))) ∧
      ∀ x : Fin (B.dZ ℓ Z) → K, B'.toF ℓ' Z' (Matrix.mulVec Gm fun k => φ (x k)) = GlobalTheory.Mem.R3.LiftLatBC.bcF φ B B' C (B.toF ℓ Z x) := by
  intro K K' _ _ _ _ _ _ G G' _ _ _ _ Pl0 Pl0' φ hφ e B B' ℓ ℓ' Z Z' s C _ h
  obtain ⟨hC, hH, hact, hnab, hZ, hX, hP, hψ⟩ := h
  obtain ⟨X', P', ψ'⟩ := ℓ'
  dsimp only at hX hP hψ
  subst hP
  obtain ⟨m, b, F, hF, hI, hb⟩ := exists_dual_family φ
  have hc : Nat.card (ℓ.P.map e.toMonoidHom) = Nat.card ℓ.P :=
    (Nat.card_congr (ℓ.P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have hl := lvlIdem_baseChange φ e B.S B.r B'.S B'.r C hact ℓ.P ℓ.ψ ψ' hψ
  have hg : B'.S.gaMat B'.r (goodAt X' (ℓ.P.map e.toMonoidHom) ψ') * C = C * (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).map φ := by
    unfold goodAt
    rw [(group_action_matrix_hom K' B'.S G' B'.r).2, (group_action_matrix_hom K B.S G B.r).2, Matrix.mul_assoc, hl, ← Matrix.mul_assoc,
      idemOf_baseChange φ e B.S B.r B'.S B'.r C hact ℓ.X X' hX, Matrix.map_mul, Matrix.mul_assoc]
  set ℓ' : Lvl K' G' := ⟨X', ℓ.P.map e.toMonoidHom, ψ'⟩ with hℓ'
  obtain ⟨A0, hA0, hE0⟩ := subE_baseChange φ C hC.1 _ _ (range_baseChange φ C hC.2 C _ _ hl)
  obtain ⟨A1, hA1, hE1⟩ := subE_baseChange φ C hC.1 _ _ (range_baseChange φ C hC.2 C _ _ hg)
  change B'.S.lvlE B'.r ℓ'.P ℓ'.ψ * A0 = C * (B.S.lvlE B.r ℓ.P ℓ.ψ).map φ at hE0
  change B'.vE ℓ' * A1 = C * (B.vE ℓ).map φ at hE1
  have hZ0 : B'.Z0 ℓ' Z' = Submodule.span K' ((fun x : Fin (B.nV ℓ) → K => A1 *ᵥ (fun k => φ (x k))) '' (B.Z0 ℓ Z : Set _)) :=
    comap_baseChange (R := K) (R' := K') φ (fun i => algebraMap (𝓞 K') K' (b i)) F hF (fun i a => ⟨F i a, rfl⟩) hb
      C hC.1 A1 hA1.2 _ _ hE1 _ _ hZ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  obtain ⟨Gm, hGm, hE2⟩ := subE_baseChange φ A1 hA1.1 _ _ hZ0
  change B'.zE ℓ' Z' * Gm = A1 * (B.zE ℓ Z).map φ at hE2
  have hvPr : B'.vPr ℓ' * C = A1 * (B.vPr ℓ).map φ := orthPr_baseChange φ hφ C A1 hA1 _ _ hH _ _ hE1
  have hHV : A1ᴴ * B'.HV ℓ' * A1 = (B.HV ℓ).map φ := by
    have h1 := gram_baseChange φ hφ C A1 _ _ hH _ _ hE1
    change A1ᴴ * ((Nat.card (ℓ.P.map e.toMonoidHom) : K')⁻¹ • ((B'.vE ℓ')ᴴ * B'.S.H * B'.vE ℓ')) * A1 =
      ((Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ)).map φ
    rw [Matrix.mul_smul, Matrix.smul_mul, h1, hc]
    generalize (B.vE ℓ)ᴴ * B.S.H * B.vE ℓ = M
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]
  have hPq : B'.Pq ℓ' Z' * A1 = Gm * (B.Pq ℓ Z).map φ := orthPr_baseChange φ hφ A1 Gm hGm _ _ hHV _ _ hE2
  have hlPr : B'.lPr ℓ' Z' * A0 = Gm * (B.lPr ℓ Z).map φ := by
    unfold BlockDat.lPr
    rw [Matrix.mul_assoc, hE0, Matrix.mul_assoc, ← Matrix.mul_assoc (B'.vPr ℓ'), hvPr, Matrix.mul_assoc A1,
      ← Matrix.mul_assoc (B'.Pq ℓ' Z'), hPq, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have hN : B'.S.lvlNab B'.r ℓ'.P ℓ'.ψ = Submodule.span (𝓞 K')
      ((fun x : Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K => A0 *ᵥ (fun k => φ (x k))) '' (B.S.lvlNab B.r ℓ.P ℓ.ψ : Set _)) :=
    comap_baseChange (R := 𝓞 K) (R' := 𝓞 K') φ b F hF hI hb
      C hC.1 A0 hA0.2 _ _ hE0 _ _ hnab _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  refine ⟨Gm, hGm, ?_, fun x => ?_⟩
  · unfold BlockDat.Tl matLat
    rw [hN]
    exact map_baseChange φ A0 Gm _ _ hlPr _
  · have hv : B'.vE ℓ' *ᵥ (B'.zE ℓ' Z' *ᵥ (Gm *ᵥ fun k => φ (x k))) =
        C *ᵥ fun k => φ ((B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ x)) k) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hE2, ← Matrix.mul_assoc, hE1,
        Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.mulVec_mulVec, map_mulVec', ← Matrix.mulVec_mulVec]
    simp only [BlockDat.toF, bcF, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [hv]

end GlobalTheory.Mem.R3.LiftLatBC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdOfEqMulIntegral
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.NormPrime

variable {R : Ranks}

theorem sqrtMinusD_mem (H : Host R) : H.sqrtMinusD ∈ H.K :=
  IntermediateField.mem_adjoin_simple_self ℚ _

theorem isTotallyComplex_K (H : Host R) : IsTotallyComplex H.K := by
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  set b : H.K := ⟨H.sqrtMinusD, sqrtMinusD_mem H⟩
  have hb : b ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simpa [b] using H.sqrtMinusD_sq
  have h1 := congrArg (InfinitePlace.embedding_of_isReal hw) hb
  rw [map_pow, map_neg, map_natCast] at h1
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hw b)]

end GlobalTheory.Mem.NormPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenAdd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Pst.NoLogTheta

section Abstract
variable {R F G : Type} [CommRing R] [IsDomain R] [Field F]

theorem eigen_add (θ : R →+* F) (σ : G → R →+* R) (τ : G → F →+* F) (c d : G → R) (t : R) (ht : t ≠ 0)
    (hθt : θ t = 0) (hker : ∀ y, θ y = 0 → t ∣ y) (hc : ∀ g, θ (c g) ≠ 0)
    (hθ : ∀ g y, θ (σ g y) = τ g (θ y)) (hσt : ∀ g, σ g t = c g * t)
    (tate : ∀ (i : ℤ) (x : F), i ≠ 0 → (∀ g, τ g x * θ (c g) ^ i = x) → x = 0)
    (n : ℕ) : ∀ y : R, (∀ g, σ g y = c g ^ n * (y + d g * t ^ (n + 1))) →
      ∃ w, y = t ^ n * w ∧ ∀ g, σ g w = w + d g * t := by
  induction n with
  | zero => intro y hy; exact ⟨y, by simp, fun g => by simpa using hy g⟩
  | succ n ih =>
    intro y hy
    have h2 : θ y = 0 := by
      refine tate (-((n + 1 : ℕ) : ℤ)) _ (by omega) fun g => ?_
      rw [zpow_neg, zpow_natCast, ← hθ, hy, map_mul, map_pow, map_add (f := _), map_mul, map_pow, hθt,
        zero_pow (Nat.succ_ne_zero _), mul_zero, add_zero]
      have := pow_ne_zero (n + 1) (hc g)
      field_simp
    obtain ⟨v, hv⟩ := hker y h2
    obtain ⟨w, hw, hw'⟩ := ih v fun g => by
      have h := hy g
      rw [hv, map_mul, hσt] at h
      have hc0 : c g ≠ 0 := fun h0 => hc g (by rw [h0, map_zero])
      apply mul_left_cancel₀ (mul_ne_zero hc0 ht)
      rw [h]
      ring
    exact ⟨w, by rw [hv, hw]; ring, hw'⟩

end Abstract

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem core_form (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.BdR l) (d : GQ l → Per.BdRp l)
    (hb : ∀ g : GQ l, Per.σD g b = b + algebraMap (Per.BdRp l) (Per.BdR l) (d g * C.j C.t)) :
    ∃ (a : ℚ_[l]) (v : Per.BdRp l), b = algebraMap (Per.BdRp l) (Per.BdR l)
      (C.o (algebraMap ℚ_[l] (Om l) a) + C.j C.t * v) := by
  have he := GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨hdom, hinj, -, hfrac⟩ := _root_.GlobalTheory.MemLoc.BdRField.bdR_isField l
  obtain ⟨hfil, hreg, hcompl, -⟩ := _root_.GlobalTheory.MemLoc.filtration_eq_xi_pow l C.ε he
  obtain ⟨-, hker, hunit, -, hθ⟩ := _root_.GlobalTheory.MemLoc.thetaD_props l
  obtain ⟨-, ht1, ht2, -⟩ := _root_.GlobalTheory.MemLoc.core_t_unit_fil l C
  obtain ⟨-, hjσ, -⟩ := _root_.GlobalTheory.MemLoc.crisP_unique_equivariant l C.j C.j_cris
  have hσD := (GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1
  have hact := _root_.GlobalTheory.MemLoc.TAct.t_act l C
  have htate := _root_.GlobalTheory.MemLoc.tate_twist_invariants l C (botExt l)
  have hast := _root_.GlobalTheory.MemLoc.invariants_finExt l (botExt l)
  generalize hx : aDp l (xi C.ε) = x at *
  obtain ⟨n, y0, hy0⟩ := hfrac C.ε he b
  rw [hx] at hy0
  generalize htt : C.j C.t = t at *
  obtain ⟨u, hu⟩ := (hfil 1 t).1 ht1
  rw [pow_one] at hu
  have huu : IsUnit u := by
    refine hunit u fun h0 => ht2 ?_
    obtain ⟨v, hv⟩ := (hfil 1 u).1 ((hker u).1 h0)
    exact (hfil 2 t).2 ⟨v, by rw [hu, hv]; ring⟩
  have ht0 : t ≠ 0 := fun h0 => ht2 (h0 ▸ zero_mem _)
  have htx : t ∣ x := by rw [hu]; exact huu.mul_right_dvd.2 dvd_rfl
  let c : GQ l → Per.BdRp l := fun g => C.o (algebraMap ℚ_[l] (Om l) ((C.χ g : ℤ_[l]) : ℚ_[l]))
  have hθc : ∀ g, Per.θD l (c g) = algebraMap ℚ_[l] ℂ_[l] ((C.χ g : ℤ_[l]) : ℚ_[l]) := fun g =>
    (C.o_sec.th _).trans rfl
  have hc : ∀ g, Per.θD l (c g) ≠ 0 := fun g => by
    rw [hθc, map_ne_zero]
    exact fun h => (C.χ g).ne_zero (PadicInt.coe_eq_zero.1 h)
  have hσt : ∀ g : GQ l, Per.σDp g t = c g * t := fun g => by
    rw [← htt, ← hjσ, hact, map_mul, InvDR.j_alg, ← C.o_sec.z]
  have hker' : ∀ y, Per.θD l y = 0 → t ∣ y := fun y hy =>
    htx.trans (by simpa using (hfil 1 y).1 ((hker y).1 hy))
  have hθt : Per.θD l t = 0 := (hker t).2 ht1
  have tate : ∀ (i : ℤ) (x : ℂ_[l]), i ≠ 0 →
      (∀ g : GQ l, Per.σC g x * Per.θD l (c g) ^ i = x) → x = 0 := fun i x hi h =>
    htate i x hi fun g _ => by simpa only [hθc] using h g
  have hy : b * algebraMap (Per.BdRp l) (Per.BdR l) t ^ n =
      algebraMap (Per.BdRp l) (Per.BdR l) (y0 * u ^ n) := by
    rw [hu, map_mul, map_mul, map_pow, ← hy0]
    ring
  generalize y0 * u ^ n = y at hy
  have hyσ : ∀ g : GQ l, Per.σDp g y = c g ^ n * (y + d g * t ^ (n + 1)) := fun g => by
    apply hinj
    rw [← hσD, ← hy, map_mul, map_pow, hσD, hσt, hb g]
    simp only [map_mul, map_pow, map_add (f := _)]
    rw [← hy]
    ring
  obtain ⟨w, hw, hw'⟩ := eigen_add (Per.θD l) (fun g : GQ l => Per.σDp g) (fun g => Per.σC g) c d t ht0
    hθt hker' hc (fun g y => hθ g y) hσt tate n y hyσ
  obtain ⟨k, hk, hkθ⟩ := hast (Per.θD l w) fun g _ => by
    rw [← hθ, hw' g, map_add (f := _), map_mul, hθt, mul_zero, add_zero]
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hk
  obtain ⟨v, hv⟩ := hker' (w - C.o (algebraMap ℚ_[l] (Om l) a))
    (by rw [map_sub, C.o_sec.th, hkθ, sub_self])
  refine ⟨a, v, ?_⟩
  rw [← hv, add_sub_cancel]
  have : IsDomain (Per.BdR l) := (_root_.GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1.isDomain
  have ht' : algebraMap (Per.BdRp l) (Per.BdR l) t ^ n ≠ 0 :=
    pow_ne_zero n ((map_ne_zero_iff _ hinj).2 ht0)
  apply mul_right_cancel₀ ht'
  rw [hy, hw, map_mul, map_pow, mul_comm]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (b : P.R.B) (c : GQ l → ℚ_[l]), (∀ g : GQ l, P.actQ g b - b = c g • P.tB) →
    ∃ a : ℚ_[l], P.ιB ((b - algebraMap ℚ_[l] P.R.B a) * tInv P) ∈ (P.PD (botExt l)).Fil 0 := by
  intro l _ P AI T b c hb
  obtain ⟨C, hC⟩ := FitsEx.exists_fits l P AI T
  have hι : ∀ g : GQ l, P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := fun g => by
    have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
    rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at this
    exact this.symm
  have ht : T.eD (P.ιB P.tB) = algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) := by
    rw [hC.ι, hC.t, Core.tB, C.ι_j]
  have hq : ∀ a : ℚ_[l], T.eD (P.ιB (algebraMap ℚ_[l] P.R.B a)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (C.o (algebraMap ℚ_[l] (Om l) a)) := fun a => by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR, hC.o]
    rfl
  obtain ⟨a, v, h⟩ := core_form l C (T.eD (P.ιB b)) (fun g => C.o (algebraMap ℚ_[l] (Om l) (c g))) fun g => by
    rw [← T.actD, hι, map_mul, ← hq, ← ht, ← map_mul, ← map_mul, ← map_add (f := _), ← map_add (f := _), ← Algebra.smul_def,
      ← hb, add_sub_cancel]
  refine ⟨a, ?_⟩
  have h1 : T.eD (P.ιB (tInv P)) * algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) = 1 := by
    rw [← ht, ← map_mul, ← map_mul, tInv_mul, map_one, map_one]
  have h2 : T.eD (P.ιB ((b - algebraMap ℚ_[l] P.R.B a) * tInv P)) =
      algebraMap (Per.BdRp l) (Per.BdR l) v := by
    rw [map_mul, map_mul, map_sub, map_sub, hq, h, map_add (f := _), map_mul]
    linear_combination algebraMap (Per.BdRp l) (Per.BdR l) v * h1
  rw [T.fil, h2]
  have h3 : (1 : Per.BdR l) ∈ Per.FilD l 0 := by
    have := (T.fil (botExt l) 0 1).1 (P.PD (botExt l)).one_mem
    rwa [map_one] at this
  have h4 := (Per.FilD l 0).smul_mem v h3
  rwa [Algebra.smul_def, mul_one] at h4

end GlobalTheory.Pst.NoLogTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyIntegral
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Pst.KummerIndep

variable {l : ℕ} [Fact l.Prime]

theorem eventually_integral (x : ℚ_[l]) :
    ∀ᶠ N : ℕ in Filter.atTop, ∃ y : ℤ_[l], (y : ℚ_[l]) = (l : ℚ_[l]) ^ N * x := by
  have h : Filter.Tendsto (fun N : ℕ => ‖(l : ℚ_[l]) ^ N * x‖) Filter.atTop (nhds 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (Padic.norm_p_lt_one (p := l))).mul_const x).norm
    simpa using this
  filter_upwards [h.eventually (ge_mem_nhds zero_lt_one)] with N hN
  exact ⟨⟨_, hN⟩, rfl⟩

theorem exists_root (P : LocPrime l) (μ : ℕ → Om l) (d : GQ l → ℤ_[l])
    (hμ : ∀ m : ℕ, μ m ^ (l ^ m) = ((l + 1 : ℕ) : Om l))
    (hd : ∀ (g : GQ l) (m : ℕ), g (μ m) = P.ζQ m ^ (PadicInt.toZModPow m (d g)).val * μ m)
    (α β r : ℤ_[l])
    (h : ∀ g : GQ l, (α : ℚ_[l]) * (kummer P g : ℚ_[l]) + β * (d g : ℚ_[l]) =
      r * ((P.χQ g : ℚ_[l]) - 1))
    (k A B : ℕ) (hA : PadicInt.toZModPow k α = A) (hB : PadicInt.toZModPow k β = B) :
    ∃ q : ℚ_[l], q ^ (l ^ k) = (l : ℚ_[l]) ^ A * ((l + 1 : ℕ) : ℚ_[l]) ^ B := by
  have : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : IsGalois ℚ_[l] (Om l) := {}
  obtain ⟨S, hS⟩ : ∃ S : ℕ, PadicInt.toZModPow k (-r) = S := ⟨_, (ZMod.natCast_zmod_val _).symm⟩
  obtain ⟨x, hx⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ_[l])
    (lRoot l k ^ A * μ k ^ B * P.ζQ k ^ S)).2 fun g => by
      have hx : ‖(P.χQ g : ℚ_[l])‖ ≤ 1 := by
        obtain ⟨a, ha, -⟩ := P.χQ_cyc g 0 1 (by simp)
        have e : (P.χQ g : ℚ_[l]) = ((P.χQ g : ℚ_[l]) - a) + a := by ring
        rw [e]
        refine (Padic.nonarchimedean _ _).trans (max_le (by simpa using ha) ?_)
        exact_mod_cast Padic.norm_int_le_one (p := l) (a : ℤ)
      let x : ℤ_[l] := ⟨P.χQ g, hx⟩
      obtain ⟨a, ha, hg⟩ := P.χQ_cyc g k (P.ζQ k) (isPrimitiveRoot_zeta P k).pow_eq_one
      have hxa : PadicInt.toZModPow k x = a := by
        rw [← sub_eq_zero, ← map_natCast (PadicInt.toZModPow k), ← map_sub, ← RingHom.mem_ker,
          PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
        exact ha
      have h1 : α * kummer P g + β * d g + (-r) * x = -r := by
        apply Subtype.ext
        have e : (x : ℚ_[l]) = P.χQ g := rfl
        have := h g
        push_cast
        rw [e]
        linear_combination this
      have h2 := congrArg (PadicInt.toZModPow k) h1
      rw [map_add (f := _), map_add (f := _), map_mul, map_mul, map_mul, hA, hB, hS, hxa] at h2
      have h3 : P.ζQ k ^ ((PadicInt.toZModPow k (kummer P g)).val * A +
          (PadicInt.toZModPow k (d g)).val * B + a * S) = P.ζQ k ^ S := by
        rw [zeta_pow_eq_iff]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        linear_combination h2
      rw [map_mul, map_mul, map_pow, map_pow, map_pow, hg, isKummer_kummer P g k, hd g k, ← h3]
      simp only [mul_pow, ← pow_mul, pow_add]
      ring
  refine ⟨x, (algebraMap ℚ_[l] (Om l)).injective ?_⟩
  rw [map_pow, hx, mul_pow, mul_pow, pow_right_comm (lRoot l k), pow_right_comm (μ k),
    pow_right_comm (P.ζQ k), lRoot_pow, hμ, (isPrimitiveRoot_zeta P k).pow_eq_one]
  simp

theorem norm_succ : ‖((l + 1 : ℕ) : ℚ_[l])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  simp

theorem dvd_of_root {k A B : ℕ} {q : ℚ_[l]}
    (h : q ^ (l ^ k) = (l : ℚ_[l]) ^ A * ((l + 1 : ℕ) : ℚ_[l]) ^ B) : l ^ k ∣ A := by
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hl1 : ((l + 1 : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  have hv : ((l + 1 : ℕ) : ℚ_[l]).valuation = 0 := by
    rw [Padic.valuation_natCast, padicValNat.eq_zero_of_not_dvd]
    · simp
    · rw [Nat.dvd_add_right dvd_rfl]
      exact (Fact.out : l.Prime).not_dvd_one
  have h2 := congrArg Padic.valuation h
  rw [Padic.valuation_mul (pow_ne_zero _ hl) (pow_ne_zero _ hl1), Padic.valuation_pow,
    Padic.valuation_pow, Padic.valuation_pow, Padic.valuation_p, hv, mul_one, mul_zero,
    add_zero] at h2
  exact Int.natCast_dvd_natCast.mp ⟨_, h2.symm⟩

theorem not_forall_root {B : ℕ} (hB : B ≠ 0)
    (h : ∀ k, ∃ q : ℚ_[l], q ^ (l ^ k) = ((l + 1 : ℕ) : ℚ_[l]) ^ B) : False := by
  have hp : l.Prime := Fact.out
  have key : ((((l + 1) ^ B) ^ (l - 1) : ℕ) : ℤ_[l]) = ((1 : ℕ) : ℤ_[l]) := by
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    cases n with
    | zero =>
      have : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
      exact Subsingleton.elim _ _
    | succ k =>
      obtain ⟨q, hq⟩ := h k
      have hn : ‖q‖ ≤ 1 := by
        have := congrArg norm hq
        rw [norm_pow, norm_pow, norm_succ, one_pow] at this
        exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.ne_zero)).mp this.le
      let y : ℤ_[l] := ⟨q, hn⟩
      have hy : y ^ (l ^ k) = (((l + 1) ^ B : ℕ) : ℤ_[l]) := by
        apply Subtype.ext
        have e : (y : ℚ_[l]) = q := rfl
        push_cast at hq ⊢
        rw [e, hq]
      have hu : IsUnit y := by
        rw [← isUnit_pow_iff (pow_ne_zero k hp.ne_zero), hy, PadicInt.isUnit_iff]
        have := norm_succ (l := l)
        rw [Nat.cast_pow, norm_pow]
        have e : ‖((l + 1 : ℕ) : ℤ_[l])‖ = 1 := by
          rw [PadicInt.norm_def, PadicInt.coe_natCast, this]
        rw [e, one_pow]
      obtain ⟨u, hu⟩ := hu.map (PadicInt.toZModPow (k + 1))
      have h1 := congrArg Units.val (ZMod.pow_totient u)
      rw [Nat.totient_prime_pow_succ hp, Units.val_pow_eq_pow_val, hu, pow_mul, ← map_pow, hy,
        ← map_pow] at h1
      rw [Nat.cast_pow, h1]
      simp
  have h2 : ((l + 1) ^ B) ^ (l - 1) = 1 := Nat.cast_injective key
  have := hp.two_le
  rw [← pow_mul, Nat.pow_eq_one] at h2
  rcases h2 with h2 | h2
  · omega
  · rcases Nat.mul_eq_zero.mp h2 with h3 | h3 <;> omega

theorem kummer_indep (l : ℕ) [Fact l.Prime] (P : LocPrime l) (μ : ℕ → Om l) (d : GQ l → ℤ_[l])
    (hμ : ∀ m : ℕ, μ m ^ (l ^ m) = ((l + 1 : ℕ) : Om l))
    (hd : ∀ (g : GQ l) (m : ℕ), g (μ m) = P.ζQ m ^ (PadicInt.toZModPow m (d g)).val * μ m)
    (α β r : ℚ_[l])
    (h : ∀ g : GQ l, α * (kummer P g : ℚ_[l]) + β * (d g : ℚ_[l]) =
      r * ((P.χQ g : ℚ_[l]) - 1)) : α = 0 ∧ β = 0 := by
  have hp : l.Prime := Fact.out
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hα : α = 0 := by
    obtain ⟨N, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := ((eventually_integral α).and
      ((eventually_integral β).and (eventually_integral r))).exists
    have h0 : a = 0 := by
      refine PadicInt.ext_of_toZModPow.mp fun k => ?_
      have : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
      obtain ⟨q, hq⟩ := exists_root P μ d hμ hd a b c
        (fun g => by rw [ha, hb, hc]; linear_combination (l : ℚ_[l]) ^ N * h g) k _ _
        (ZMod.natCast_zmod_val _).symm (ZMod.natCast_zmod_val _).symm
      rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow k a), map_zero, ZMod.natCast_eq_zero_iff]
      exact dvd_of_root hq
    rw [h0] at ha
    exact (mul_eq_zero.mp ha.symm).resolve_left (pow_ne_zero _ hl)
  refine ⟨hα, by_contra fun hβ => ?_⟩
  obtain ⟨N, c, hc⟩ := (eventually_integral (r / β)).exists
  refine not_forall_root (l := l) (B := l ^ N) (pow_ne_zero _ hp.ne_zero) fun k => ?_
  have := exists_root P μ d hμ hd 0 ((l ^ N : ℕ) : ℤ_[l]) c (fun g => by
    have h1 := h g
    rw [hα] at h1
    rw [hc]
    push_cast
    field_simp
    linear_combination (l : ℚ_[l]) ^ N * h1) k 0 (l ^ N) (by simp) (map_natCast _ _)
  simpa only [pow_zero, one_mul] using this

end GlobalTheory.Pst.KummerIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsOfSemilinearStatement
section
open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_of_semilinear_alt : ∀ {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K'] {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type} (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (L : B.S.Forms →+ B'.S.Forms),
  (∀ (a : K) (f : B.S.Forms), L (a • f) = φ a • L f) →
  LinearIndependent K' (fun k => L (B.S.basis k)) → ⊤ ≤ Submodule.span K' (Set.range fun k => L (B.S.basis k)) →
  (∀ f g : B.S.Forms, B'.S.csum (L f : B'.S.Cl → B'.S.V) (L g) = φ (B.S.csum f g)) →
  (∀ (g : G) (f : B.S.Forms), B'.r (e g) (L f) = L (B.r g f)) →
  (∀ f' : B'.S.Forms, (∀ c, (f' : B'.S.Cl → B'.S.V) c ∈ B'.S.Nab c) ↔ f' ∈ Submodule.span (𝓞 K') (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c})) →
  Z' = Submodule.span K' (L '' (Z : Set B.S.Forms)) →
  ∃ C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K', Function.Bijective C.mulVec ∧
    Cᴴ * B'.S.H * C = B.S.H.map φ ∧
    (∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ) ∧
    B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K))) ∧
    B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K))) := by
  first | exact @GlobalTheory.Mem.R3.DefLatBC.forms_of_semilinear | exact GlobalTheory.Mem.R3.DefLatBC.forms_of_semilinear | (intros; apply GlobalTheory.Mem.R3.DefLatBC.forms_of_semilinear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideCardEqOfCoord
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem rowSide_card_eq_of_coord {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (X : RowSide D EE) {n d : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE)
    (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V) : n = d := by
  let bC : Module.Basis X.RR.ι ℂ EE := Module.Basis.mk X.jEE_basis.1 X.jEE_basis.2.ge
  let bL : Module.Basis (Fin d) D.what₂.LL X.RR.V := (Pi.basisFun D.what₂.LL (Fin d)).map e
  have e1 : Fin n ≃ X.RR.ι := b.toBasis.indexEquiv bC
  have e2 : X.RR.ι ≃ Fin d := X.RR.b.indexEquiv bL
  simpa using Fintype.card_congr (e1.trans e2)

end GlobalTheory
end

