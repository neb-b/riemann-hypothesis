module

public import Formalism.LocalToGlobal.Columns.Bundle0024
public import Formalism.LocalToGlobal.Columns.Bundle0020
public import Formalism.LocalToGlobal.Columns.TiedLv
public import Formalism.LocalToGlobal.Columns.Bundle0023
public import Formalism.LocalToGlobal.Columns.Bundle0022
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.Columns.Bundle0019

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.LocalLevelIsKOneEverywhere
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d)

theorem th_gram_eq (hS : SpStd d.toColBase) (i : ℕ) (hi : i ≤ d.R.m) : (d.sp.X i).gram = 1 := by
  refine Matrix.ext fun x y => ?_
  show (d.sp.X i).hT ((d.sp.X i).frame x) ((d.sp.X i).frame y) = _
  rw [hS.X_on i hi, Matrix.one_apply]

theorem th_gram0_eq (hS : SpStd d.toColBase) : d.sp.gram0 = 1 := by
  refine Matrix.ext fun x y => ?_
  show (d.sp.X 0).hT ((d.sp.X 0).frame _) ((d.sp.X 0).frame _) = _
  rw [hS.X_on 0 (Nat.zero_le _), Matrix.one_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]

theorem th_crdLat_eq (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) (c : StCl (Pr := d.Pr) d.W d.lev u i) :
    Formalism.L2.Herm.crdLat (d.sp.X i) (d.clsLat u i c) = Formalism.L2.Forms.reL (d.sp.X_rank i hi).symm (d.repr u i c).1.L := by
  unfold Formalism.L2.Herm.crdLat ColDat.clsLat Formalism.L2.Forms.reL
  rw [dite_eq_left hi, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  funext j
  show (d.sp.X i).frame.equivFun ((d.crd i hi).symm x) j = _
  unfold ColDat.crd
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem th_crdLat0_eq (u : d.what₂.Word) (c : StCl (Pr := d.Pr) d.W d.lev u 0) :
    d.sp.crdLat0 (d.clsLat u 0 c) = Formalism.L2.Forms.reL (Formalism.L2.Forms.rank_eq_first_level d.R).symm (d.repr u 0 c).1.L := by
  unfold Spaces.crdLat0 ColDat.clsLat Formalism.L2.Forms.reL
  rw [dite_eq_left (Nat.zero_le _), ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  funext j
  show d.sp.crd0 ((d.crd 0 (Nat.zero_le _)).symm x) j = _
  unfold ColDat.crd Spaces.crd0
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

def hCrd (hS : SpStd d.toColBase) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    HCrd d.Pr (d.R.N i) fun c : StCl (Pr := d.Pr) d.W d.lev u i => (d.repr u i c).1.L where
  n' := (d.sp.X i).rank
  hn := d.sp.X_rank i hi
  J := (d.sp.X i).gram
  hJ := th_gram_eq hS i hi
  f := d.R.f
  hf := d.f_eq.symm
  bad := plUnder d.X.F d.Pr.vGs
  hbad := rfl
  lat := fun c => Formalism.L2.Herm.crdLat (d.sp.X i) (d.clsLat u i c)
  hlat := fun c => th_crdLat_eq u i hi c

def hCrd0 (hS : SpStd d.toColBase) (u : d.what₂.Word) :
    HCrd d.Pr (d.R.N 0) fun c : StCl (Pr := d.Pr) d.W d.lev u 0 => (d.repr u 0 c).1.L where
  n' := d.R.k
  hn := Formalism.L2.Forms.rank_eq_first_level d.R
  J := d.sp.gram0
  hJ := th_gram0_eq hS
  f := d.R.f
  hf := d.f_eq.symm
  bad := plUnder d.X.F d.Pr.vGs
  hbad := rfl
  lat := fun c => d.sp.crdLat0 (d.clsLat u 0 c)
  hlat := fun c => th_crdLat0_eq u c

def LocalLevelIsKOneEverywhere (d : ColDat) : Prop := ∀ (u : d.what₂.Word) (i : ℕ), LocalLevelIsKOneAtT d.sp.cm u (d.lev i)

def IwAll (d : ColDat) (S : GSplit (Pr := d.Pr) d.sp.cm) : Prop := ∀ u : d.what₂.Word, IwLoc d.sp.cm u (d.lev 0) S.sp

def hermPack (hS : SpStd d.toColBase) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :=
  levPack d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (hK u i) (hCrd hS u i hi)

def hermPack0 (hS : SpStd d.toColBase) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (u : d.what₂.Word) :=
  levPack d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) (colDia (X := d.X) (Pr := d.Pr) d.R u 0) (d.repr u 0) (hP u 0)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.spec c) (hK u 0) (hCrd0 hS u)

def hermLev0 (hS : SpStd d.toColBase) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)
    (u : d.what₂.Word) :
    ColLevel d.R d.host.F d.host.E d.sp d.host.g (d.chain a u) (d.atT a u) (fun i c => d.clsLat u i c) :=
  LevPack.toCol (sp := d.sp) (C := d.chain a u) (A := d.atT a u) (clsLat := fun i c => d.clsLat u i c)
    (hermPack0 hS hP hK u) S.sp S.sp_sig
    (levPack_iw d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) S.sp _ _ _ _ _ (hI u) (hCrd0 hS u))
    (exists_place_over_first_prime d.hX d.hPr).choose (exists_place_over_first_prime d.hX d.hPr).choose_spec

def hermCols (hS : SpStd d.toColBase) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S) :
    CH.HermCols (d.colRec a) where
  lev0 := fun u => hermLev0 a hS hP hK S hI u
  lev := fun u i _ hm => LevPack.toStep (S := d.sp.X i) (lat := d.clsLat u i) (hermPack hS hP hK u i hm)
  cls := fun u i _ hm => LevPack.toCls (S := d.sp.X i) (lat := d.clsLat u i) (hermPack hS hP hK u i hm)
  vT := fun u => tieEV d.sp.cm d.hX d.hPr u
  Fv := fun u v => tieFv d.sp.cm d.hX d.hPr u v

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedUpDnLoc
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.P
open Formalism.L2.DIV (Pl kP St redAt redFn resS)

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem updn_den {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P) (a : E ⊗[F] Formalism.L2.Herm.Af F)
    (h : prV (E := E) v a ∈ Formalism.BasicNotions.intV E v) :
    ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ iA F E (algebraMap (𝓞 E) E t) * a ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨D, hD, hDa⟩ := levelaf_denom (E := E) a
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  set DE : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) D with hDE
  have hDE0 : DE ≠ 0 := by
    rw [hDE, Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    exact hD
  have hI : (Ideal.span {p * DE} : Ideal (𝓞 E)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hp0 hDE0
  obtain ⟨q, hq⟩ := Formalism.L2.DIV.cmpS_surj (F := F) _ hI (Ideal.Quotient.mk _ (Formalism.L2.DIV.lc_eps E v))
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hq' : Ideal.Quotient.mk (Formalism.L2.DIV.idS F (Ideal.span {p * DE})) (Formalism.L2.DIV.oToS F E t) =
      Ideal.Quotient.mk _ (Formalism.L2.DIV.lc_eps E v) := hq
  have hd := Ideal.Quotient.eq.1 hq'
  unfold Formalism.L2.DIV.idS at hd
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hd
  obtain ⟨y, hy⟩ := hd
  have ht : Formalism.L2.DIV.oToS F E t = Formalism.L2.DIV.lc_eps E v + y * Formalism.L2.DIV.oToS F E p * Formalism.L2.DIV.oToS F E DE := by
    rw [mul_assoc, ← map_mul, hy]; ring
  refine ⟨t, ?_, ?_⟩
  · intro htP
    have h1 := congrArg (resS F P) ht
    rw [map_add (f := _), map_mul, map_mul, Formalism.L2.DIV.lc_res_eps P v hov, Formalism.L2.DIV.resS_oToS, Formalism.L2.DIV.resS_oToS,
      Ideal.Quotient.eq_zero_iff_mem.2 htP, Ideal.Quotient.eq_zero_iff_mem.2 hp, mul_zero, zero_mul, add_zero] at h1
    exact zero_ne_one h1
  · have hC : ((Formalism.L2.DIV.oToS F E DE : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = levelafC E D := by
      rw [Formalism.L2.DIV.levelafC_eq_incl, ← iA_coe, hDE, ← IsScalarTower.algebraMap_apply]
    rw [iA_coe, ht]
    have e : ((Formalism.L2.DIV.lc_eps E v + y * Formalism.L2.DIV.oToS F E p * Formalism.L2.DIV.oToS F E DE : Formalism.L2.Herm.intAf F E) :
        E ⊗[F] Formalism.L2.Herm.Af F) * a = afsplitIE v (prV (E := E) v a) +
          ((y * Formalism.L2.DIV.oToS F E p : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * (levelafC E D * a) := by
      rw [afsplit_decomp, ← hC, Subring.coe_add, Subring.coe_mul, add_mul, mul_assoc]
      rfl
    rw [e]
    exact add_mem (afsplit_IE_int v _ h) (mul_mem (y * Formalism.L2.DIV.oToS F E p).2 hDa)

variable {n : ℕ}

theorem updn_prV_pullV {v : HeightOneSpectrum (𝓞 F)} {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') (z : Fin n → E) (i : Fin n) :
    prV (E := E) v (pullV x z i) = prV (E := E) v (pullV x' z i) := by
  have h' : bc (prV (E := E) v) x⁻¹ = bc (prV (E := E) v) x'⁻¹ := by rw [map_inv, map_inv, h]
  unfold pullV
  simp only [Matrix.mulVec, dotProduct]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul]
  congr 1
  exact congrArg (fun g : GL (Fin n) (E ⊗[F] v.adicCompletion F) =>
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) h'

variable [StarRing E]

theorem localized_globalLattice_le {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') :
    localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) ≤ localization₂ P.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n)) := by
  classical
  intro z hz
  obtain ⟨s, hs, hsz⟩ := (mem_locP P _ z).1 hz
  have h1 : ∀ i, ∃ t : 𝓞 E, t ∉ P.asIdeal ∧
      iA F E (algebraMap (𝓞 E) E t) * pullV x' (s • z) i ∈ Formalism.L2.Herm.intAf F E := fun i =>
    updn_den hov _ (by
      rw [← updn_prV_pullV h]
      exact afsplit_prV_int v _ ((mem_globLat x _).1 hsz i))
  choose t ht hti using h1
  have hT : (∏ i, t i) ∉ P.asIdeal := by
    intro hm
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
    exact ht i hi
  refine (mem_locP P _ z).2 ⟨(∏ i, t i) * s, fun hm => (P.isPrime.mem_or_mem hm).elim hT hs, ?_⟩
  rw [mul_smul, mem_globLat]
  intro i
  rw [pullV_osmul, ← Finset.prod_erase_mul Finset.univ t (Finset.mem_univ i), map_mul, map_mul, mul_assoc]
  exact mul_mem (iA_mem _) (hti i)

theorem updn_mem_loc {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') :
    localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) = localization₂ P.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n)) :=
  le_antisymm (localized_globalLattice_le hov h) (localized_globalLattice_le hov h.symm)

theorem updn_red_loc {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') {z : Fin n → E}
    (hz : z ∈ localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))) (i : Fin n) :
    redA P (pullV x z i) = redA P (pullV x' z i) := by
  have hz' : z ∈ localization₂ P.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n)) := localized_globalLattice_le hov h hz
  obtain ⟨s, hs, hsz⟩ := pullV_den hz
  obtain ⟨s', hs', hsz'⟩ := pullV_den hz'
  have hss : s * s' ∉ P.asIdeal := fun hm => (P.isPrime.mem_or_mem hm).elim hs hs'
  have m1 : iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x z i ∈ Formalism.L2.Herm.intAf F E := by
    rw [mul_comm s s', map_mul, map_mul, mul_assoc]
    exact mul_mem (iA_mem _) (hsz i)
  have m2 : iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x' z i ∈ Formalism.L2.Herm.intAf F E := by
    rw [map_mul, map_mul, mul_assoc]
    exact mul_mem (iA_mem _) (hsz' i)
  apply mul_left_cancel₀ (mk_ne_zero hss)
  rw [redA_spec P hss m1, redA_spec P hss m2, ← sub_eq_zero, ← map_sub]
  refine Formalism.L2.DIV.resS_eq_zero_of_prV P v hov _ ?_
  show prV (E := E) v (iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x z i -
    iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x' z i) = 0
  rw [map_sub, map_mul (prV (E := E) v), map_mul (prV (E := E) v), updn_prV_pullV h, sub_self]

variable [NeZero n] (ST SG : Finset (Pl E))

theorem updn_f_loc {v : HeightOneSpectrum (𝓞 F)} (P : ST) (hov : IsOver v P.1)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') :
    (decoRaw ST SG x).f P = (decoRaw ST SG x').f P := by
  funext z
  show (open Classical in if z ∈ localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
      then redA P.1 (pullV x z (lastIdx n)) else 0) =
    (open Classical in if z ∈ localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n))
      then redA P.1 (pullV x' z (lastIdx n)) else 0)
  rw [← updn_mem_loc hov h]
  by_cases hz : z ∈ localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
  · rw [if_pos hz, if_pos hz, updn_red_loc hov h hz]
  · rw [if_neg hz, if_neg hz]

theorem updn_be_loc {v : HeightOneSpectrum (𝓞 F)} (w : SG) (hov : IsOver v w.1)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') :
    (decoRaw ST SG x).be w = (decoRaw ST SG x').be w := by
  funext z
  show (open Classical in if z ∈ localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
      then fun i => redA w.1 (pullV x z i) else 0) =
    (open Classical in if z ∈ localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n))
      then fun i => redA w.1 (pullV x' z i) else 0)
  rw [← updn_mem_loc hov h]
  by_cases hz : z ∈ localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
  · rw [if_pos hz, if_pos hz]
    funext i
    exact updn_red_loc hov h hz i
  · rw [if_neg hz, if_neg hz]

structure Deco.SameOff (v : HeightOneSpectrum (𝓞 F)) (d d' : Deco E n ST SG) : Prop where
  N : ∀ Q : Pl E, ¬ IsOver v Q → localization₂ Q.asIdeal d.N = localization₂ Q.asIdeal d'.N
  f : ∀ Q : ST, ¬ IsOver v Q.1 → d.f Q = d'.f Q
  be : ∀ w : SG, ¬ IsOver v w.1 → d.be w = d'.be w

end Loc

section Move

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG (E := E) (n := n) (SG := SG)))

end Move

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedXpV
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xp_half (R : Ranks) : R.m * (R.t + 1) / 2 = R.m * ((R.t + 1) / 2) := by
  obtain ⟨b, hb⟩ := R.t_odd
  have h : R.t + 1 = 2 * (b + 1) := by omega
  rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

theorem xp_sgTrue_eq {R : Ranks} (S : RowPar R) : S.sgTrue = shW S.sg ((R.m * (R.t + 1) / 2 : ℕ) : ℤ) := by
  unfold RowPar.sgTrue shiftW shW
  congr 1
  funext i
  rw [xp_half]
  push_cast
  ring

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ValuationPosIffMemSeen
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)


open Classical in
theorem th_pull_tauOf (w : HeightOneSpectrum (𝓞 X.K)) (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) (P : {P // P ∈ Pr.vT u}) :
    pullW (tauOfR hX hPr u w P) w = if seenC Pr u w then P.1 else conjPrime₂ P.1 := by
  have := hX.nonempty_Tau
  have e : tauOfR hX hPr u w P = tauOfC w P.1 := by
    unfold tauOfR
    rw [dite_eq_left hw]
    rfl
  rw [e]
  by_cases hs : seenC Pr u w
  · rw [if_pos hs]
    exact (tauOfC_spec hX hPr u w hw P).resolve_right (hs.not_bar hPr _ P)
  · rw [if_neg hs]
    refine (tauOfC_spec hX hPr u w hw P).resolve_left fun h => hs (seenC_of_one hPr (τ := tauOfC w P.1) ?_)
    rw [show pullW (tauOfC w P.1) w = P.1 from h]
    exact P.2

end Gen

variable {d : ColDat} (a : ColArgs d)

open Classical in
theorem valuation_pos_iff_mem_seen (hH : HostHyp d) (u : d.what₂.Word) (w : d.what₂.places.Pl) (hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal)
    (v : {P // P ∈ d.Pr.vT u}) (x : 𝓞 d.X.E) :
    (0 : WithTop ℤ) < d.what₂.places.val w ((d.X.embO (tauOfR d.hX d.hPr u (d.plEq w) v) x : 𝓞 d.X.K) : d.X.K) ↔
      x ∈ (if decide (seenC d.Pr u (d.plEq w)) = true then v.1.asIdeal else conjIdeal (K := d.X.E) v.1.asIdeal) := by
  rw [att_val_pos d.what₂.places d.plEq hH.val_eq w]
  have h1 : d.X.embO (tauOfR d.hX d.hPr u (d.plEq w) v) x ∈ (d.plEq w).asIdeal ↔
      x ∈ (pullW (tauOfR d.hX d.hPr u (d.plEq w) v) (d.plEq w)).asIdeal := Iff.rfl
  rw [h1, th_pull_tauOf d.hX d.hPr u (d.plEq w) hT v]
  by_cases hs : seenC d.Pr u (d.plEq w)
  · rw [if_pos hs, if_pos (decide_eq_true hs)]
  · rw [if_neg hs, if_neg (by simpa using hs), conjIdeal_asIdeal]

theorem th_seen (hH : HostHyp d) (u : d.what₂.Word) : AtTSeen (atTTied a hH u) := by
  intro w hw v x y hy
  have hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal := by
    have := att_resChar_mem d.what₂.places d.plEq hH.val_eq w
    rw [hw] at this
    exact this
  have hy' : y = ((d.X.embO (tauOfR d.hX d.hPr u (d.plEq w) v) x : 𝓞 d.X.K) : d.X.K) := by
    apply d.what₂.embLL.injective
    rw [hy]
    show d.host.φ₀ _ = d.what₂.embLL (d.embE _)
    rw [← hH.embE_φ₀]
    rfl
  have hPv : (atTTied a hH u).Pv v = v.1.asIdeal := lv_Pv_eq a hH u v
  rw [hy', hPv]
  exact valuation_pos_iff_mem_seen hH u w hT v x

end Formalism.L2.Col
end
end

