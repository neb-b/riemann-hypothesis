module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0647
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalCharacterComponentsLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

open scoped TensorProduct

namespace GlobalTheory.FlatPlace

theorem finComp_eq_toAd {D : D7} (z : AE D) :
    GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E z = GlobalTheory.StdFrames.toAd D (Formalism.IndefR.Datum.toEAf D z) := by
  have key : ∀ y : Af D.host.F ⊗[D.host.F] D.host.E,
      GlobalTheory.LFun.toFinAd D.host.F D.host.E y = GlobalTheory.StdFrames.toAd D (Formalism.IndefR.Lev.swapAE D y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x =>
      rw [GlobalTheory.LFun.toFinAd_tmul, mul_comm]
      exact (GlobalTheory.StdFrames.toAd_spec D x a).symm
    | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]
  exact key _

theorem iota_add_eq_locIdele {D : D7} {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) (x : (Kw w)ˣ) :
    p.ι x + (1 - p.e) = (GlobalTheory.LFun.locIdele D.host.F w x : AE D) := by
  classical
  have e_ι : ∀ y, p.e * p.ι y = p.ι y := fun y => by rw [← p.ι_π, p.π_ι]
  have he1 : p.e = atPl w 1 := by
    rw [← hp.2.2 1]
    have := p.ι_π 1
    rw [map_one, mul_one] at this
    exact this.symm
  have hfc : ∀ z Q, GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E z Q = GlobalTheory.StdFrames.cpt Q (Formalism.IndefR.Datum.toEAf D z) :=
    fun z Q => by rw [finComp_eq_toAd]; rfl
  have hδ : GlobalTheory.CMPrimeIdele.IsDelta (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) w p.e := by
    refine ⟨by rw [he1]; exact (atPl_spec w 1).1, by rw [hfc, he1, (atPl_spec w 1).2, Pi.single_eq_same], fun Q hQ => ?_⟩
    rw [hfc, he1, (atPl_spec w 1).2, Pi.single_eq_of_ne hQ]
  have := GlobalTheory.LFun.EulerTie.glue_eq_locIdele hδ (a := p.ι x) (u := x)
    (by rw [hfc, hp.2.2, (atPl_spec w _).2, Pi.single_eq_same])
  rwa [e_ι] at this

theorem isComp_attChr {D : D7} {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) (c η : (AE D)ˣ →* Circle)
    (μ e : (Kw w)ˣ →* ℂˣ) (hc : ∀ y, ((c (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) = ((μ y : ℂˣ) : ℂ))
    (he : ∀ y, ((η (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) = ((e y : ℂˣ) : ℂ)) (n k : ℕ)
    (hk : (k + 1) % 2 = if Odd n then 1 else 0) :
    p.IsComp (Formalism.IndefR.Lift.attChr c η n) (μ / e ^ ((k + 1) % 2)) := by
  intro x a ha
  have ha' : a = GlobalTheory.LFun.locIdele D.host.F w x := Units.ext (ha.trans (iota_add_eq_locIdele hp x))
  subst ha'
  rw [hk]
  unfold Formalism.IndefR.Lift.attChr
  split_ifs with h
  · simp only [pow_one, MonoidHom.div_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_div_eq_div_val,
      Circle.coe_mul, Circle.coe_inv, hc, he, div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  · simp only [pow_zero, div_one, hc]

end GlobalTheory.FlatPlace

namespace GlobalTheory.FlatPlace

theorem chrP_big : Big fun ch => ChrP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t w hw p hp
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  refine ⟨fun x => ?_, (((Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w hw).square 0 hm 0 hm).cond, fun j hj => ?_⟩
  · rw [hp.2.2 x] <;> rfl
  have hE : ChrEq (R.toLevCh.mu t (j + 1)) (muBase R.toLevCh (j + 1) * R.toLevCh.xiH t) := by
    have h1 : muBase R.toLevCh (j + 1) = R.toLevCh.C.mu0 ⟨j, hj⟩ := dif_pos hj
    rw [h1]
    exact GlobalTheory.TowerCharRead.chrEq_mul (hL.mu0 ⟨j, hj⟩) (hL.xi t)
  have hmu : ∀ y, ((R.toLevCh.mu t (j + 1) (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) =
      (((locGrid ch.G t w).mu (j + 1) y : ℂˣ) : ℂ) :=
    fun y => congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq hE w)
  have heta : ∀ y, ((R.toLevCh.eta (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) =
      (((locGrid ch.G t w).eta y : ℂˣ) : ℂ) :=
    fun y => congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq hL.eta w)
  have r0 := (rank_vertex ch.G t w (X := (D.R.m, j)) ⟨le_rfl, hj.le⟩).symm
  have r1 := (rank_vertex ch.G t w (X := (D.R.m, j + 1)) ⟨le_rfl, hj⟩).symm
  have hstep : (locGrid ch.G t w).rank (D.R.m, j + 1) = (locGrid ch.G t w).rank (D.R.m, j) + D.R.t := by
    show D.R.r + (j + 1) * D.R.t + D.R.m * sLen D = D.R.r + j * D.R.t + D.R.m * sLen D + D.R.t
    ring
  obtain ⟨c, hc'⟩ := D.R.t_odd
  refine ⟨?_, ?_⟩
  · refine isComp_attChr hp _ _ _ _ hmu heta _ _ ?_
    rw [r0, hstep, hc']
    split_ifs with h
    · obtain ⟨d, hd⟩ := h; omega
    · rw [Nat.not_odd_iff_even] at h; obtain ⟨d, hd⟩ := h; omega
  · refine isComp_attChr hp _ _ _ _ hmu heta _ _ ?_
    rw [r1, hstep, hc']
    split_ifs with h
    · obtain ⟨d, hd⟩ := h; omega
    · rw [Nat.not_odd_iff_even] at h; obtain ⟨d, hd⟩ := h; omega

end GlobalTheory.FlatPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegLineLatticeAndBesselCoreLatticeSelfDualSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.RowShape

variable {D : D7}

theorem nLine_gram (D : D7) : (GlobalTheory.SeeSaw.Model.nLine D).gram = -1 := by
  refine Matrix.ext fun i j => ?_
  refine (congrArg Neg.neg (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral 1
    (fun _ => false) 1 0 i j)).trans ?_
  rw [Matrix.neg_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h, Formalism.BasicNotions.Examples₂.sgn] <;> first | exact rfl | exact fun e => h e

theorem mem_latPi {S : HSp D} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {y : Fin S.rank → D.host.E} :
    y ∈ latPi S I ↔ ∀ i, y i ∈ I := by
  simp [latPi, Submodule.mem_pi]

theorem isSelfDualC_latPi {S : HSp D} (hg : S.gram = -1) {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hI : I ≠ 0)
    (hII : I * GlobalTheory.SeeSaw.conjFI D I = 1) : IsSelfDualC S (latPi S I) := by
  set J := GlobalTheory.SeeSaw.conjFI D I with hJdef
  have hJ : J ≠ 0 := fun h => hI (by rw [h, mul_zero] at hII; exact absurd hII.symm one_ne_zero)
  have hstar : ∀ x : D.host.E, star x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hmemJ : ∀ x : D.host.E, x ∈ J ↔ star x ∈ I := fun x => by rw [hstar]; exact GlobalTheory.SeeSaw.mem_conjFI
  have hpair : ∀ x y : Fin S.rank → D.host.E, ∑ a, ∑ b, star (x a) * S.gram a b * y b = -∑ a, star (x a) * y a := by
    intro x y
    rw [hg, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [Matrix.neg_apply, Matrix.one_apply, Ne.symm hb]
    · simp
  have hIeq : I = J⁻¹ := eq_inv_of_mul_eq_one_left hII
  obtain ⟨a0, ha0, ha00⟩ : ∃ a ∈ I, a ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hI (by
      ext x
      rw [FractionalIdeal.mem_zero_iff]
      exact ⟨hcon x, fun h => h ▸ Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)⟩)
  refine ⟨⟨Submodule.fg_pi fun _ => FractionalIdeal.fg_of_isNoetherianRing le_rfl _, ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · intro s _ hs
    exact (LinearIndependent.iff_fractionRing (𝓞 D.host.E) D.host.E).mp hs
  · rw [hpair]
    have hy' := mem_latPi.1 hy
    have hx' := mem_latPi.1 hx
    have hs : -∑ a, star (x a) * y a ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun a _ => ?_)
      rw [← hII, mul_comm]
      exact FractionalIdeal.mul_mem_mul ((hmemJ _).2 (by rw [star_star]; exact hx' a)) (hy' a)
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 hs
    exact ⟨b, by rw [RingOfIntegers.coe_eq_algebraMap]; exact hb⟩
  · refine mem_latPi.2 fun i => ?_
    rw [hIeq, FractionalIdeal.mem_inv_iff hJ]
    intro t ht
    have hx : (Pi.single i (star t) : Fin S.rank → D.host.E) ∈ latPi S I := mem_latPi.2 fun k => by
      by_cases hk : k = i
      · subst hk; simpa using (hmemJ t).1 ht
      · rw [Pi.single_eq_of_ne hk]; exact Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)
    obtain ⟨b, hb⟩ := h _ hx
    rw [hpair, Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)] at hb
    simp only [Pi.single_eq_same, star_star] at hb
    refine (FractionalIdeal.mem_one_iff _).2 ⟨-b, ?_⟩
    rw [map_neg, ← RingOfIntegers.coe_eq_algebraMap, hb, mul_comm]
    ring

theorem conjFI_AAbar (D : D7) : GlobalTheory.SeeSaw.conjFI D D.host.AAbar = D.host.AA := by
  rw [← GlobalTheory.SeeSaw.conjFI_AA]
  ext x
  rw [GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.conj_conj_host]

theorem lineId_ne_zero (D : D7) (j : ℕ) : lineId D j ≠ 0 := by
  have hA := GlobalTheory.FinPl.LocGen.AA_ne_zero D
  have hB : D.host.AAbar ≠ 0 := by
    rw [← GlobalTheory.SeeSaw.conjFI_AA]; exact (map_ne_zero _).2 hA
  exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB))

theorem lineId_mul_conj (D : D7) (j : ℕ) : lineId D j * GlobalTheory.SeeSaw.conjFI D (lineId D j) = 1 := by
  have hA := GlobalTheory.FinPl.LocGen.AA_ne_zero D
  have hB : D.host.AAbar ≠ 0 := by
    rw [← GlobalTheory.SeeSaw.conjFI_AA]; exact (map_ne_zero _).2 hA
  unfold lineId
  rw [map_mul, map_inv₀, map_pow, map_pow, GlobalTheory.SeeSaw.conjFI_AA, conjFI_AAbar]
  have hA' := pow_ne_zero ((D.R.m - 2 - j) / 2 + 1) hA
  have hB' := pow_ne_zero ((D.R.m - 2 - j) / 2 + 1) hB
  field_simp

theorem coreL_selfDual_split : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ, j + 2 * σ + 2 = D.R.m → IsSelfDualC _ (GlobalTheory.RowShape.lineL D j) ∧
    IsSelfDualC _ (GlobalTheory.RowShape.coreL ch.G j) ∧ ∀ v, GlobalTheory.FinPl.OrthAt (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (GlobalTheory.RowShape.coreL ch.G j) (ch.G.Λ (.top j)) (GlobalTheory.RowShape.lineL D j) v := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ j σ hj
  have hL : IsSelfDualC _ (lineL D j) := isSelfDualC_latPi (nLine_gram D) (lineId_ne_zero D j) (lineId_mul_conj D j)
  have hX : IsSelfDualC _ (ch.G.Λ (.top j)) :=
    (ch.G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => by cases h)).sd
  exact ⟨hL, GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO D _ _ _ _ _ _ hX hL,
    fun v => GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ _ _ _ v⟩

end GlobalTheory.RowShape
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFiniteDatumLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ProdDatum

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

section Gen

variable {D : D7} {S T : HSp D}

def tens (a b : AE D) (Φ Ψ : WO S T → ℂ) : WO S T → ℂ :=
  fun y => if IsHalf (a + b) y then Φ (a • y) * Ψ (b • y) else 0

theorem half_iff {a : AE D} {y : WO S T} : IsHalf a y ↔ a • y = y :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

theorem tens_comm (a b : AE D) (Φ Ψ : WO S T → ℂ) : tens a b Φ Ψ = tens b a Ψ Φ := by
  funext y
  unfold tens
  rw [add_comm b a, mul_comm]

def tensL (a b : AE D) (Φ : WO S T → ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := tens a b Φ
  map_add' Ψ Ψ' := by
    funext y
    simp only [tens, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c Ψ := by
    funext y
    simp only [tens, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem half_add_iff {e : AE D} {u : WO S T} (hu : IsHalf e u) (t : WO S T) : IsHalf e (t + u) ↔ IsHalf e t := by
  rw [half_iff] at hu
  rw [half_iff, half_iff, smul_add, hu, add_left_inj]

theorem aux1 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (a : R) (k l : ℕ) (u : M) :
    a • ((k * l) • u) = k • (l • (a • u)) := by rw [smul_comm a, mul_smul]

theorem aux2 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {a : R} (ha : a * a = a) (l : ℕ) (u : M) :
    a • (l • (a • u)) = l • (a • u) := by rw [smul_comm a l, smul_smul a, ha]

theorem aux3 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {a b : R} (k l : ℕ) {t : M} (h : (a + b) • t = t) :
    (k * l) • t = l • (k • (a • t)) + k • (l • (b • t)) := by
  rw [← mul_smul l k, ← mul_smul k l, mul_comm l k, ← smul_add, ← add_smul, h]

theorem aux4 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {a : R} (k : ℕ) {t : M} (h : a • t = t) :
    a • (k • t) = k • t := by rw [smul_comm, h]

variable {a b : AE D} {Λ : AddSubgroup (WO S T)}

theorem tens_sb (ha : a * a = a) (hb : b * b = b) (hΛa : ∀ u ∈ Λ, a • u ∈ Λ) (hΛb : ∀ u ∈ Λ, b • u ∈ Λ)
    {Φ Ψ : WO S T → ℂ} (hΦ : IsSBHalf a Λ Φ) (hΨ : IsSBHalf b Λ Ψ) : IsSBHalf (a + b) Λ (tens a b Φ Ψ) := by
  obtain ⟨-, k, hk, h2, h3⟩ := hΦ
  obtain ⟨-, l, hl, g2, g3⟩ := hΨ
  refine ⟨fun t ht => ?_, k * l, Nat.mul_pos hk hl, fun u hu hh t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (if_neg h)
  · have hh' : IsHalf (a + b) ((k * l) • u) := half_iff.2 (aux4 _ (half_iff.1 hh))
    unfold tens
    by_cases h : IsHalf (a + b) t
    · rw [if_pos h, if_pos ((half_add_iff hh' t).2 h), smul_add, smul_add]
      have e1 : a • ((k * l) • u) = k • (l • (a • u)) := aux1 a k l u
      have e2 : b • ((k * l) • u) = l • (k • (b • u)) := by rw [mul_comm k l]; exact aux1 b l k u
      rw [e1, e2, h2 _ (nsmul_mem (hΛa u hu) l) (half_iff.2 (aux2 ha l u)),
        g2 _ (nsmul_mem (hΛb u hu) k) (half_iff.2 (aux2 hb k u))]
    · rw [if_neg h, if_neg fun h' => h ((half_add_iff hh' t).1 h')]
  · unfold tens at ht
    by_cases h : IsHalf (a + b) t
    · rw [if_pos h] at ht
      have e : (k * l) • t = l • (k • (a • t)) + k • (l • (b • t)) := aux3 k l (half_iff.1 h)
      rw [e]
      exact add_mem (nsmul_mem (h3 _ (left_ne_zero_of_mul ht)) l) (nsmul_mem (g3 _ (right_ne_zero_of_mul ht)) k)
    · exact absurd (if_neg h) ht

theorem tens_ind (ha : a * a = a) (hb : b * b = b) (hΛa : ∀ u ∈ Λ, a • u ∈ Λ) (hΛb : ∀ u ∈ Λ, b • u ∈ Λ) :
    tens a b (halfInd a Λ) (halfInd b Λ) = halfInd (a + b) Λ := by
  funext y
  have h1 : IsHalf a (a • y) := half_iff.2 (by rw [smul_smul, ha])
  have h2 : IsHalf b (b • y) := half_iff.2 (by rw [smul_smul, hb])
  unfold tens halfInd
  by_cases h : IsHalf (a + b) y
  · rw [if_pos h]
    by_cases hy : y ∈ Λ
    · rw [if_pos ⟨hΛa y hy, h1⟩, if_pos ⟨hΛb y hy, h2⟩, if_pos ⟨hy, h⟩, one_mul]
    · rw [if_neg (fun h' : y ∈ Λ ∧ _ => hy h'.1)]
      by_cases hay : a • y ∈ Λ
      · have : b • y ∉ Λ := fun hby => hy (by
          have := add_mem hay hby
          rwa [← add_smul, half_iff.1 h] at this)
        rw [if_neg (fun h' : b • y ∈ Λ ∧ _ => this h'.1), mul_zero]
      · rw [if_neg (fun h' : a • y ∈ Λ ∧ _ => hay h'.1), zero_mul]
  · rw [if_neg h, if_neg (fun h' : y ∈ Λ ∧ _ => h h'.2)]

theorem tens_model (ψ : AddChar (AF D.host.F) ℂ) (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0)
    (hΛa : ∀ u ∈ Λ, a • u ∈ Λ) (hΛb : ∀ u ∈ Λ, b • u ∈ Λ) {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm) {Φ : WO S T → ℂ} (hΦ : IsSBHalf a Λ Φ) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) b Λ 1 (Tm (tens a b Φ (halfInd b Λ))) (Tm ∘ₗ tensL a b Φ) := by
  refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, by rw [one_smul]; rfl⟩
  · have hx1 : b • x = x := half_iff.1 hx
    have hx0 : a • x = 0 := by rw [← hx1, smul_smul, hab, zero_smul]
    have hx2 : IsHalf (a + b) x := half_iff.2 (by rw [add_smul, hx0, hx1, zero_add])
    have e : tens a b Φ (fun t => Ψ (t + x)) = fun t => tens a b Φ Ψ (t + x) := by
      funext t
      simp only [tens, half_add_iff hx2 t, smul_add, hx0, hx1, add_zero]
    change Tm (tens a b Φ (fun t => Ψ (t + x))) = heisO ψ S T x (Tm (tens a b Φ Ψ))
    rw [e]
    exact hT.trans _ (tens_sb ha hb hΛa hΛb hΦ hΨ) x hx2
  · have hy1 : cA D b • y = y := half_iff.1 hy
    have hy2 : IsHalf (cA D (a + b)) y := half_iff.2 (by
      rw [RingHom.map_add (f := _), add_smul, hy1, ← hy1, smul_smul, ← RingHom.map_mul, hab, RingHom.map_zero, zero_smul, zero_add])
    have e : tens a b Φ (fun t => ψ (symplO S T t y) * Ψ t) = fun t => ψ (symplO S T t y) * tens a b Φ Ψ t := by
      funext t
      simp only [tens]
      rw [symplO_smul, hy1]
      split_ifs <;> ring
    change Tm (tens a b Φ (fun t => ψ (symplO S T t y) * Ψ t)) = heisO ψ S T y (Tm (tens a b Φ Ψ))
    rw [e]
    exact hT.modul _ (tens_sb ha hb hΛa hΛb hΦ hΨ) y hy2

end Gen

theorem orth_of_idemSum {D : D7} {a b : AE D} {P Q R : Finset (Pl D.host.E)} (ha : IsIdemSum a P) (hb : IsIdemSum b Q)
    (h : IsIdemSum (a + b) R) : a * b = 0 ∧ (a + cA D a) * (b + cA D b) = 0 := by
  have a2 := idemSum_mul_self ha
  have b2 := idemSum_mul_self hb
  have s2 := idemSum_mul_self h
  have hab : a * b = 0 := by
    have h2 : incA D 2⁻¹ * (1 + 1) = 1 := by
      rw [← (incA D).map_one, ← RingHom.map_add (f := _), ← RingHom.map_mul]
      congr 1
      norm_num
    linear_combination incA D 2⁻¹ * (s2 - a2 - b2) - a * b * h2
  have h1 := h.2
  rw [RingHom.map_add (f := _)] at h1
  have ha' := ha.2
  have hb' := hb.2
  have k1 : a * cA D b = 0 := by
    linear_combination a * h1 - (cA D a + cA D b) * a2 - ha' - (cA D a + cA D b) * hab
  have k2 : b * cA D a = 0 := by
    linear_combination h1 - ha' - hb' - k1
  have k3 : cA D a * cA D b = 0 := by rw [← RingHom.map_mul, hab, RingHom.map_zero]
  exact ⟨hab, by linear_combination hab + k1 + k2 + k3⟩

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {t : T}


set_option maxHeartbeats 1000000 in
theorem exists_prod {p : Pair T} (hS : IsSelfDualC (G.pS p) (G.latS p)) (hT : IsSelfDualC (G.pT p) (G.latT p))
    (d₁ d₂ : FinDatum G t p) (c₁ c₂ : WO (G.pS p) (G.pT p) →₀ ℂ) (he : IsIdemSum (d₁.e + d₂.e) (d₁.P ∪ d₂.P))
    (h₁ : IsCombOf W d₁ c₁) (h₂ : IsCombOf W d₂ c₂) :
    ∃ (d : FinDatum G t p) (c : WO (G.pS p) (G.pT p) →₀ ℂ), d.P = d₁.P ∪ d₂.P ∧ d.e = d₁.e + d₂.e ∧ IsCombOf W d c ∧
      (∀ y, IsHalf d.e y → d.fn y = d₁.fn (d₁.e • y) * d₂.fn (d₂.e • y)) ∧
      ∀ f, comb W.ψ _ _ c f = comb W.ψ _ _ c₁ (comb W.ψ _ _ c₂ f) := by
  have a2 := idemSum_mul_self d₁.e_is
  have b2 := idemSum_mul_self d₂.e_is
  obtain ⟨hab, horth⟩ := orth_of_idemSum d₁.e_is d₂.e_is he
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True,
      a • u ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True := fun a ha u hu =>
    GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu
  have HC := GlobalTheory.HeisComb.main D W.ψ (G.pS p) (G.pT p)
  obtain ⟨c, hsupp, hc⟩ := HC.1 c₁ c₂
  let d : FinDatum G t p :=
    { P := d₁.P ∪ d₂.P
      P_over := fun w hw => (Finset.mem_union.1 hw).elim (d₁.P_over w) (d₂.P_over w)
      e := d₁.e + d₂.e
      e_is := he
      fn := tens d₁.e d₂.e d₁.fn d₂.fn
      sb := tens_sb a2 b2 (hsm _ a2) (hsm _ b2) d₁.sb d₂.sb
      z := 1
      z_cen := (FinDatum.vacuum G t p).z_cen
      z_supp := (FinDatum.vacuum G t p).z_supp }
  refine ⟨d, c, rfl, rfl, ⟨fun u hu => ?_, fun u hu => ?_, fun f₀ hth hvac => ⟨?_, fun Tm hTm => ?_⟩⟩,
    fun y hy => if_pos hy, hc⟩
  · obtain ⟨x, hx, y, hy, rfl⟩ := hsupp u hu
    rw [Matrix.map_add _ (fun a b => RingHom.map_add _ a b), h₁.1 x hx, h₂.1 y hy, add_zero]
  · obtain ⟨x, hx, y, hy, rfl⟩ := hsupp u hu
    intro i j
    have k1 := h₁.2.1 x hx i j
    have k2 := h₂.2.1 y hy i j
    change (d₁.e + d₂.e + cA D (d₁.e + d₂.e)) * (x i j + y i j) = x i j + y i j
    rw [RingHom.map_add (f := _)]
    linear_combination (1 - d₂.e - cA D d₂.e) * k1 + (1 - d₁.e - cA D d₁.e) * k2 + (x i j + y i j) * horth
  · exact (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _ hS hT d.P d.e d.e_is f₀ hth hvac).1
  · obtain ⟨c', k1, k2⟩ := GlobalTheory.CombsExist.exists_comb_model W.ψ _ _ _ _ d₂.e d₂.fn W.ψ_std hS hT b2 d₂.e_is.2
      (infPart_idemSum d₂.e_is) d₂.sb
    have hT1 : IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) (d₁.e + d₂.e)
      (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) 1 f₀ Tm := hTm
    have hT2 := hT1
    rw [add_comm] at hT2
    have v := hT1.vac
    rw [one_smul] at v
    have m2 := tens_model W.ψ a2 b2 hab (hsm _ a2) (hsm _ b2) hT1 (GlobalTheory.isSBHalf_halfInd d₁.e _)
    rw [tens_ind a2 b2 (hsm _ a2) (hsm _ b2), v] at m2
    have m1 := tens_model W.ψ b2 a2 (by rw [mul_comm, hab]) (hsm _ b2) (hsm _ a2) hT2 (GlobalTheory.isSBHalf_halfInd d₂.e _)
    rw [tens_ind b2 a2 (hsm _ b2) (hsm _ a2), add_comm, v] at m1
    have m3 := tens_model W.ψ a2 b2 hab (hsm _ a2) (hsm _ b2) hT1 d₁.sb
    have e2 : comb W.ψ _ _ c₂ f₀ = comb W.ψ _ _ c' f₀ := ((h₂.2.2 f₀ hth hvac).2 _ m2).trans (k2 f₀ _ m2).symm
    have e1 := (h₁.2.2 f₀ hth hvac).2 _ m1
    have e3 := k2 _ _ m3
    have hcomm := HC.2.1 c₁ c' (fun x hx y hy => HC.2.2.2 _ _ x y
      (by rw [RingHom.map_add (f := _), Formalism.L2.Theta.cA_cA, add_comm]) horth (h₁.2.1 x hx) (k1 y hy).2) f₀
    rw [hc, e2, hcomm, e1]
    refine Eq.trans ?_ e3
    congr 1
    exact congrArg Tm (tens_comm _ _ _ _)

theorem prod_datum : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (j : Fin D.R.m) (d₁ d₂ : FinDatum ch.G t (.top t j)) (c₁ c₂ : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), IsIdemSum (d₁.e + d₂.e) (d₁.P ∪ d₂.P) → IsCombOf ch.W d₁ c₁ → IsCombOf ch.W d₂ c₂ → ∃ (d : FinDatum ch.G t (.top t j)) (c : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), d.P = d₁.P ∪ d₂.P ∧ d.e = d₁.e + d₂.e ∧ IsCombOf ch.W d c ∧ (∀ y, IsHalf d.e y → d.fn y = d₁.fn (d₁.e • y) * d₂.fn (d₂.e • y)) ∧ ∀ f, comb ch.W.ψ _ _ c f = comb ch.W.ψ _ _ c₁ (comb ch.W.ψ _ _ c₂ f) :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ t j d₁ d₂ c₁ c₂ =>
    exists_prod ch.W (p := .top t j) (ch.G.isV (X := .top j) j.2.le fun _ h => by cases h).sd
      (ch.G.isV (X := .top (j + 1)) j.2 fun _ h => by cases h).sd d₁ d₂ c₁ c₂⟩⟩

end GlobalTheory.ProdDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceScalarsMulEqOppositePathEdgeFactorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceScalars_mul_eq_oppositePath_edgeFactors : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ w ∈ locPl G t, (∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) →
    GlobalTheory.RowVacScalar.splitScal G (.chi j D.R.m) w (G.toPair (.chi j D.R.m) 1 (moved S j k)).1
                 (G.toPair (.chi j D.R.m) 1 (moved S j k)).2 *
      GlobalTheory.RowVacScalar.splitScal G (.chi (j + 1) D.R.m) w (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).1
        (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2 =
    ((oppositePath D.R.m).map ((locGrid G t w).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  first | exact @GlobalTheory.RowVacScalar.splitScal_mul_eq_oppositePath | exact GlobalTheory.RowVacScalar.splitScal_mul_eq_oppositePath | (intros; apply GlobalTheory.RowVacScalar.splitScal_mul_eq_oppositePath <;> assumption)
end

