module

public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.SymGSupport
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDd
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.NoOpStep
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0008
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.FrameZeroLe
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics
open Formalism.MainNotions.G.WittFrameLocaliserOrders

namespace G2

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

theorem frame_zero_le (hV : Fr.Valid L₁ N₁) (j : ℤ) : Fr.fr j 0 ≤ Fr.fr j (r - 1) := by
  obtain ⟨_, _, hinc, _⟩ := hV
  have key : ∀ i, i ≤ r - 1 → Fr.fr j 0 ≤ Fr.fr j i := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih => intro hi; exact (ih (by omega)).trans (hinc j i (by omega)).le
  exact key (r - 1) le_rfl

theorem zstep (hV : Fr.Valid L₁ N₁) (a : ℤ) : Fr.fr a (r - 1) < Fr.fr (a + 1) (r - 1) := (hV.2.2.2.1 a).trans_le (frame_zero_le hV (a + 1))

theorem zmono (hV : Fr.Valid L₁ N₁) (a b : ℤ) (hab : a ≤ b) : Fr.fr a (r - 1) ≤ Fr.fr b (r - 1) := by
  have key : ∀ k : ℕ, Fr.fr a (r - 1) ≤ Fr.fr (a + k) (r - 1) := by
    intro k
    induction k with
    | zero => simpa using (le_rfl : Fr.fr a (r - 1) ≤ Fr.fr a (r - 1))
    | succ k ih =>
      have h := ih.trans (zstep hV (a + k)).le
      simpa only [Nat.cast_succ, add_assoc] using h
  have h := key (b - a).toNat
  have heq : a + (↑(b - a).toNat : ℤ) = b := by omega
  simpa only [heq] using h

theorem seg' (hV : Fr.Valid L₁ N₁) {J : ℕ} [NeZero J] {nL : ZMod J → ℕ}
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (x : TL J nL r) :
    Fr.fr (segZ x.1 - 1) (r - 1) < posTL Fr x ∧ posTL Fr x ≤ Fr.fr (segZ x.1) (r - 1) := by
  obtain ⟨j, l | m⟩ := x
  · have h := (mem_LLset Fr _ _).1 (llPos_mem Fr (segZ j) l.val (by rw [← hnL]; exact l.isLt))
    exact ⟨h.1.1, le_trans (le_of_lt h.1.2) (frame_zero_le hV (segZ j))⟩
  · have hr : 1 ≤ r := by have := m.isLt; omega
    have h := posTL_seg Fr hV hr hnL (⟨j, Sum.inr m⟩ : TL J nL r)
    exact ⟨h.1, h.2.1⟩

end G2

theorem restGeo : RestGeo := by
  intro n' r _ Fr L₁ N₁ hV p J _ nL hJ hnL j hj y hy x' hpos
  unfold lowP
  apply pow_dvd_pow
  obtain ⟨h1, h2⟩ := G2.seg' hV hnL x'
  have s0 := segZ_nonneg x'.1
  have s1 := segZ_lt x'.1
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hy
  obtain ⟨⟨y1, y2⟩, -⟩ := hy
  have hper := hV.2.1
  have hJ' : (J : ℤ) = (Fr.J : ℤ) := by exact_mod_cast hJ
  have hjJ : (j : ℤ) < (Fr.J : ℤ) := by exact_mod_cast hj
  have hj0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
  have hlast : Fr.fr ((Fr.J : ℤ) - 1) (r - 1) = Fr.fr (-1) (r - 1) + n' := by
    have := hper (-1) (r - 1)
    rw [← this]; congr 1
  have w1 := G2.zmono hV (-1) (segZ x'.1 - 1) (by omega)
  have w2 := G2.zmono hV (segZ x'.1) ((Fr.J : ℤ) - 1) (by omega)
  have w3 := G2.zmono hV (j : ℤ) ((Fr.J : ℤ) - 1) (by omega)
  have hwin : Fr.fr (-1) (r - 1) + 1 ≤ posTL Fr x' ∧ posTL Fr x' < Fr.fr (-1) (r - 1) + 1 + n' := by
    constructor <;> omega
  unfold Frames.dist
  apply Int.toNat_le_toNat
  by_cases hc : Fr.fr (-1) (r - 1) + 1 ≤ y
  · have hy' : posTL Fr x' = y := residue_position_injective_window n' _ _ _ hwin ⟨hc, by omega⟩ hpos
    have hs : segZ x'.1 ≤ (j : ℤ) := by
      by_contra hlt
      have := G2.zmono hV (j : ℤ) (segZ x'.1 - 1) (by omega)
      omega
    have := G2.zmono hV (segZ x'.1) (j : ℤ) hs
    omega
  · have a1 : Fr.fr ((j : ℤ) - 1 + Fr.J) 0 = Fr.fr ((j : ℤ) - 1) 0 + n' := hper _ _
    have a2 := hV.2.2.2.1 ((j : ℤ) - 2 + Fr.J)
    have a3 : (j : ℤ) - 2 + Fr.J + 1 = (j : ℤ) - 1 + Fr.J := by ring
    rw [a3] at a2
    have hJ1 : (1 : ℤ) ≤ (Fr.J : ℤ) := by omega
    have a4 := G2.zmono hV (-1) ((j : ℤ) - 2 + Fr.J) (by omega)
    have hy' : posTL Fr x' = y + n' :=
      residue_position_injective_window n' _ _ _ hwin ⟨by omega, by omega⟩ (by rw [DdG.posOf_add_n]; exact hpos)
    have a5 : Fr.fr ((j : ℤ) + Fr.J) (r - 1) = Fr.fr (j : ℤ) (r - 1) + n' := hper _ _
    have a6 := G2.zmono hV (segZ x'.1) ((j : ℤ) + Fr.J) (by omega)
    omega

end Formalism.MainNotions.PairMembershipBlocks
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.GeoTouch
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics

theorem geoTop : GeoTop := by
  intro n' r _ _ Fr L₁ N₁ hV J _ nL hJ hnL s hs
  have hr : 1 ≤ r := NeZero.pos r
  obtain ⟨x0, hx0⟩ := posTL_surj Fr hV hr hJ hnL s hs
  refine ⟨x0, hx0, fun x' hx' => ?_⟩
  exact posTL_inj Fr hV hr hJ hnL (hx'.trans hx0.symm)

theorem geoTouch : GeoTouch := by
  intro n' r _ _ Fr L₁ N₁ hV J _ nL hJ hnL x0 j u hu hx
  have hr : 1 ≤ r := NeZero.pos r
  have hu' : u < (Fr.LLset (segZ j)).card + r := by rw [← hnL]; exact hu
  unfold touchT
  rcases hx with (⟨l, hl, hlt⟩ | ⟨m, hm, hlt⟩) | ⟨m, hm⟩
  · subst hl
    have hl' : l.val < (Fr.LLset (segZ j)).card := by rw [← hnL]; exact l.isLt
    refine ⟨llPos Fr (segZ j) l.val, (LL_sub_letters hV hr _ _ (llPos_mem Fr (segZ j) l.val hl')).1, rfl, ?_⟩
    rw [← posU_ll (Fr := Fr) (segZ j) l.val hl']
    exact (posU_le_iff hV (segZ j) _ _ (by omega) hu').2 (by omega)
  · subst hm
    have hm' := m.isLt
    refine ⟨Fr.fr (segZ j) (r - 1 - m.val), fr_mem_letters hV hr _ _ (by omega), rfl, ?_⟩
    rw [← posU_fr (Fr := Fr) (segZ j) (r - 1 - m.val)]
    refine (posU_le_iff hV (segZ j) _ _ (by omega) hu').2 ?_
    rw [← hnL]
    omega
  · subst hm
    have hm' := m.isLt
    obtain ⟨s, hs, hsh⟩ := DdG.shift Fr hV.2.1 hJ (j - 1)
    rw [sub_add_cancel] at hsh
    refine ⟨Fr.fr (segZ j - 1) (r - 1 - m.val), w_mem_letters hV hr _ _ (by omega), ?_,
      (w_lt_posU hV hr _ _ _ (by omega) hu').le⟩
    show _ = posOf n' (Fr.fr (segZ (j - 1)) (r - 1 - m.val))
    rw [(hsh (r - 1 - m.val)).1]
    rcases hs with rfl | rfl
    · rw [add_zero]
    · rw [DdG.posOf_add_n]

end Formalism.MainNotions.PairMembershipBlocks
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.SumFiberMultideg
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G3

theorem sum_fiber_multideg {r : ℕ} (μ : ℤ × Fin r →₀ ℕ) (y : ℤ) :
    ∑ v ∈ μ.support, (if v.1 = y then μ v else 0) = multideg μ y := by
  unfold multideg
  rw [← Finset.sum_filter]
  have h1 : ∑ c : Fin r, μ (y, c) = ∑ v ∈ (Finset.univ.image fun c : Fin r => (y, c)), μ v := by
    rw [Finset.sum_image]
    intro a _ b _ h
    exact (Prod.mk.inj h).2
  rw [h1]
  apply Finset.sum_subset
  · intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_image]
    exact ⟨v.2, Finset.mem_univ _, by rw [← hv.2]⟩
  · intro v hv hnot
    rw [Finset.mem_image] at hv
    obtain ⟨c, -, rfl⟩ := hv
    by_contra h
    exact hnot (Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 h, rfl⟩)

theorem lkW {n' r : ℕ} (Fr : Frames n' r) (jz : ℤ) (μ : ℤ × Fin r →₀ ℕ) :
    wDeg (wSet Fr jz) μ ≤ ∑ m' : Fin r, multideg μ (Fr.fr (jz - 1) (r - 1 - m'.val)) := by
  unfold wDeg
  calc ∑ v ∈ μ.support, (if v.1 ∈ wSet Fr jz then μ v else 0)
      ≤ ∑ v ∈ μ.support, ∑ m' : Fin r, (if v.1 = Fr.fr (jz - 1) (r - 1 - m'.val) then μ v else 0) := by
        refine Finset.sum_le_sum fun v _ => ?_
        split_ifs with h
        · obtain ⟨m, hm⟩ := h
          calc μ v = (if v.1 = Fr.fr (jz - 1) (r - 1 - m.val) then μ v else 0) := by rw [if_pos hm]
            _ ≤ _ := Finset.single_le_sum
              (f := fun m' : Fin r => if v.1 = Fr.fr (jz - 1) (r - 1 - m'.val) then μ v else 0)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
        · exact Nat.zero_le _
    _ = ∑ m' : Fin r, ∑ v ∈ μ.support, (if v.1 = Fr.fr (jz - 1) (r - 1 - m'.val) then μ v else 0) := Finset.sum_comm
    _ = ∑ m' : Fin r, multideg μ (Fr.fr (jz - 1) (r - 1 - m'.val)) :=
        Finset.sum_congr rfl fun m' _ => sum_fiber_multideg μ _

end Formalism.MainNotions.PairMembershipBlocks
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.SupportedOfSupport
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.TraceSpectra
open Formalism.MainNotions.TestSideWords.TwistedFiltration.G3 Formalism.MainNotions.G.GLWeightTheory

namespace Lk

theorem homComp_eq {ι : Type} {s : ℕ} {Kf : Type} [Field Kf] (d : ι → ℕ) (H : MvPolynomial (ι × Fin s) Kf) :
    homComp d H = compD d H := rfl

theorem compD_support {ι : Type} {s : ℕ} {Kf : Type} [Field Kf] (d : ι → ℕ) (H : MvPolynomial (ι × Fin s) Kf)
    (mo : ι × Fin s →₀ ℕ) (hmo : mo ∈ (compD d H).support) : mo ∈ H.support ∧ ∀ x, multideg mo x = d x := by
  unfold compD at hmo
  obtain ⟨a, ha, hmo'⟩ := Finset.mem_biUnion.1 (support_sum hmo)
  have := support_monomial_subset hmo'
  rw [Finset.mem_singleton] at this
  subst this
  exact ⟨(Finset.mem_filter.1 ha).1, (Finset.mem_filter.1 ha).2⟩

theorem compD_sum {ι κ : Type} {s : ℕ} {Kf : Type} [Field Kf] (d : ι → ℕ) (T : Finset κ)
    (f : κ → MvPolynomial (ι × Fin s) Kf) : compD d (∑ i ∈ T, f i) = ∑ i ∈ T, compD d (f i) :=
  map_sum (AddMonoidHom.mk ⟨compD d, T5.compD_zero d⟩ (T5.compD_add d)) f T

theorem compD_eq_zero {ι : Type} {s : ℕ} {Kf : Type} [Field Kf] (d : ι → ℕ) (H : MvPolynomial (ι × Fin s) Kf)
    (h : ∀ mo ∈ H.support, ∃ x, multideg mo x ≠ d x) : compD d H = 0 := by
  unfold compD
  refine Finset.sum_eq_zero fun mo hmo => ?_
  obtain ⟨x, hx⟩ := h mo (Finset.mem_filter.1 hmo).1
  exact absurd ((Finset.mem_filter.1 hmo).2 x) hx

theorem supported_of_support {τ R : Type*} [CommSemiring R] {s : Set τ} {P Q : MvPolynomial τ R}
    (h : P.support ⊆ Q.support) (hQ : Q ∈ supported R s) : P ∈ supported R s := by
  rw [mem_supported] at hQ ⊢
  intro v hv
  obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support v).1 (Finset.mem_coe.1 hv)
  exact hQ (Finset.mem_coe.2 ((mem_vars_iff_mem_support v).2 ⟨d, h hd, hvd⟩))

theorem multideg_add {ι : Type} {s : ℕ} (a b : ι × Fin s →₀ ℕ) (x : ι) :
    multideg (a + b) x = multideg a x + multideg b x := by
  unfold multideg
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]

theorem geZ_sum {Kf : Type} [Field Kf] {ι κ : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι) (T : Finset κ)
    (f : κ → MvPolynomial (ι × Fin n) Kf) (t : ℝ) (h : ∀ i ∈ T, geZ (valS LL S (f i)) t) :
    geZ (valS LL S (∑ i ∈ T, f i)) t := by
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, valS_zero_eq_top]
    exact geZ_top _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact geZ_mono (mul_valS_add _ _ _ _) (geZ_min (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem le_of_geZ {x : WithTop ℤ} {t : ℝ} (h : geZ x t) : ((⌈t⌉ : ℤ) : WithTop ℤ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe k => exact WithTop.coe_le_coe.2 (Int.ceil_le.2 (h k rfl))

theorem geZ_coe {k : ℤ} {t : ℝ} (h : t ≤ (k : ℝ)) : geZ ((k : ℤ) : WithTop ℤ) t := by
  intro k' hk'
  have : k = k' := WithTop.coe_injective hk'
  rw [← this]
  exact h

end Lk

theorem restLink_of (hNN : ValNN) (hHD : HomDec) (hLL : LinkL) (hDg : LkDeg) (hVr : LkVars) (hTr : RestTr)
    (hW : ∀ {n' r : ℕ} (Fr : Frames n' r) (jz : ℤ) (μ : ℤ × Fin r →₀ ℕ),
      wDeg (wSet Fr jz) μ ≤ ∑ m' : Fin r, multideg μ (Fr.fr (jz - 1) (r - 1 - m'.val))) : RestLink := by
  intro p _ n' r K m _ _ _ O _ _ _ _ hk Fr L₁ N₁ hV hn J _ Dt hT hJ A hA l hl ga hga t ht dPl j mm hm
  obtain ⟨hEq, hcov⟩ := hTr p n' r K m O hk Fr L₁ N₁ hV hn J Dt hT A hA l hl ga hga
  have hp : 0 < p := (Fact.out : p.Prime).pos
  set μ0 := plMon Fr p hk Dt.nL (l.mapDomain (castV hk) + ga) with hμ0
  set u := Dt.nL j + (r - 1 - mm.val) with hu
  have hur : u < Dt.nL j + r := by omega
  set Ab : ZMod J → MvPolynomial (ℤ × Fin r) (KK O) :=
    fun j' => MvPolynomial.map (algebraMap O (KK O)) (A (segZ j')) with hAb
  set Rst : MvPolynomial (TL J Dt.nL r × Fin r) (KK O) :=
    monomial μ0 1 * ∏ j' ∈ Finset.univ.erase j, PhiJ Fr Dt j' (Ab j') with hRst
  have e1 : levP Fr p hk Dt.nL (zPl p O hk Fr A l ga) = Rst * PhiJ Fr Dt j (Ab j) := by
    rw [hEq, hRst]
    have : ∏ j' : ZMod J, Dt.ph (chi Fr Dt.nL (KK O) j' (MvPolynomial.map (algebraMap O (KK O)) (A (segZ j')))) =
        PhiJ Fr Dt j (Ab j) * ∏ j' ∈ Finset.univ.erase j, PhiJ Fr Dt j' (Ab j') :=
      (Finset.mul_prod_erase Finset.univ (fun j' => PhiJ Fr Dt j' (Ab j')) (Finset.mem_univ j)).symm
    rw [this]
    ring

  have hR0 : 0 ≤ valS Dt.trueLet (Dt.TSet j mm) Rst := by
    apply hNN
    intro v hv hvT
    rcases Finset.mem_union.1 (vars_mul _ _ hv) with h1 | h1
    · rw [vars_monomial one_ne_zero] at h1
      have h2 : μ0 v ≠ 0 := Finsupp.mem_support_iff.1 h1
      obtain ⟨⟨j'', s⟩, a⟩ := v
      cases s with
      | inl ll =>
        by_contra hs
        have hs' : Dt.sgn j'' ll = false := by
          have : Dt.trueLet.vec ⟨j'', Sum.inl ll⟩ = Dt.sgn j'' ll := rfl
          rw [this] at hs
          simpa using hs
        exact h2 (hcov j'' ll a hs')
      | inr m' => rfl
    · obtain ⟨j', hj', h2⟩ := Finset.mem_biUnion.1 (vars_prod _ h1)
      have hne : j' ≠ j := (Finset.mem_erase.1 hj').1
      rcases hVr p n' r O Fr J Dt j' (Ab j') v h2 with ⟨ll, h3⟩ | ⟨j'', m', h3⟩
      · exfalso
        rw [h3] at hvT
        rcases hvT with ⟨l', h4⟩ | ⟨m', _, h4⟩
        · exact hne (congrArg Sigma.fst h4)
        · exact hne (congrArg Sigma.fst h4)
      · rw [h3]
        rfl

  obtain ⟨Dl, hDl⟩ := hHD (KK O) ℤ r (Ab j)
  have e2 : compD dPl (Rst * PhiJ Fr Dt j (Ab j)) =
      ∑ δ ∈ Dl, compD dPl (Rst * PhiJ Fr Dt j (compD δ (Ab j))) := by
    conv_lhs => rw [hDl]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum, Lk.compD_sum]
    rfl
  rw [e1, e2]
  refine Lk.geZ_sum _ _ _ _ _ fun δ _ => ?_
  set F := compD δ (Ab j) with hF
  have hjv : j.val < Fr.J := by
    rw [← hT.1]
    exact ZMod.val_lt j
  have hAbS : Ab j ∈ supported (KK O) {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j)} := by
    have h1 := hA j.val hjv
    rw [mem_supported] at h1 ⊢
    exact fun v hv => h1 (Finset.mem_coe.2 (vars_map (A (segZ j)) (algebraMap O (KK O)) (Finset.mem_coe.1 hv)))
  have hFS : F ∈ supported (KK O) {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j)} :=
    Lk.supported_of_support (fun mo hmo => (Lk.compD_support δ (Ab j) mo hmo).1) hAbS
  have hFd : ∀ μ ∈ F.support, ∀ y, multideg μ y = δ y := fun μ hμ => (Lk.compD_support δ (Ab j) μ hμ).2
  have hdeg := hDg p n' r O Fr L₁ N₁ hV J Dt hT hJ j F hFS δ hFd
  by_cases hbig : ∃ m' : Fin r, dPl ⟨j - 1, Sum.inr m'⟩ <
      multideg μ0 ⟨j - 1, Sum.inr m'⟩ + Dt.P (j - 1) m' * δ (Fr.fr (segZ j - 1) (r - 1 - m'.val))
  ·
    obtain ⟨m', hm'⟩ := hbig
    rw [Lk.compD_eq_zero, valS_zero_eq_top]
    · exact geZ_top _
    · intro mo hmo
      refine ⟨⟨j - 1, Sum.inr m'⟩, ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul _ _ hmo)
      obtain ⟨a0, ha0, c, _, rfl⟩ := Finset.mem_add.1 (support_mul _ _ ha)
      have h0 := support_monomial_subset ha0
      rw [Finset.mem_singleton] at h0
      subst h0
      rw [Lk.multideg_add, Lk.multideg_add, hdeg b hb m']
      omega
  · push Not at hbig
    set dw : ℕ := ∑ m' : Fin r, δ (Fr.fr (segZ j - 1) (r - 1 - m'.val)) with hdw
    have hwd : ∀ μ ∈ F.support, wDeg (wSet Fr (segZ j)) μ ≤ dw := by
      intro μ hμ
      refine le_trans (hW Fr (segZ j) μ) (le_of_eq ?_)
      exact Finset.sum_congr rfl fun m' _ => hFd μ hμ _
    have hdwB : (dw : ℝ) ≤ dwB Fr hk Dt dPl (l.mapDomain (castV hk) + ga) j := by
      unfold dwB
      rw [hdw]
      push_cast
      refine Finset.sum_le_sum fun m' _ => ?_
      have hP : (0 : ℝ) < (Dt.P (j - 1) m' : ℝ) := by
        have : 0 < Dt.P (j - 1) m' := pow_pos hp _
        exact_mod_cast this
      rw [le_div_iff₀ hP]
      have h1 := hbig m'
      have h2 : δ (Fr.fr (segZ j - 1) (r - 1 - m'.val)) * Dt.P (j - 1) m' ≤
          dPl ⟨j - 1, Sum.inr m'⟩ - multideg μ0 ⟨j - 1, Sum.inr m'⟩ := by
        rw [mul_comm]
        omega
      exact_mod_cast h2
    have h1 : ((⌈t j u⌉ : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < posU Fr (Dt.nL j) (segZ j) u} F := by
      refine le_trans (Lk.le_of_geZ (ht j u hur)) ?_
      have h2 := (valComp (KK O) ℤ r LZ {y | y < posU Fr (Dt.nL j) (segZ j) u} (Ab j) δ).1
      rw [Lk.homComp_eq] at h2
      refine le_trans (le_of_eq ?_) h2
      exact (Formalism.MainNotions.G.Joints.StandardMonomialSpace.valS_map (algebraMap O (KK O)) (IsFractionRing.injective O (KK O)) LZ _ _).symm
    have h3 := hLL p n' r O Fr L₁ N₁ hV hn J Dt hT hJ j mm hm F hFS dw hwd ⌈t j u⌉ h1
    have h4 : ((⌈t j u⌉ - dw : ℤ) : WithTop ℤ) ≤
        valS Dt.trueLet (Dt.TSet j mm) (compD dPl (Rst * PhiJ Fr Dt j F)) := by
      have h5 := (valComp (KK O) _ r Dt.trueLet (Dt.TSet j mm) (Rst * PhiJ Fr Dt j F) dPl).1
      rw [Lk.homComp_eq] at h5
      refine le_trans ?_ h5
      rw [mul_valS_mul]
      calc ((⌈t j u⌉ - dw : ℤ) : WithTop ℤ) = 0 + ((⌈t j u⌉ - dw : ℤ) : WithTop ℤ) := (zero_add _).symm
        _ ≤ _ := add_le_add hR0 h3
    refine geZ_mono h4 (Lk.geZ_coe ?_)
    have := Int.le_ceil (t j u)
    push_cast
    linarith

end Formalism.MainNotions.PairMembershipBlocks
end
end

