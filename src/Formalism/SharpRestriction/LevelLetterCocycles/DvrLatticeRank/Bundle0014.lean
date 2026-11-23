module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfDict
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0011
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UnivLinkPfB

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfL
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}
    (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)


open Classical in
def framepf_gco (x : ↥(NcS W T (c - 1))) : Fin Bs.r → PowerSeries O :=
  if h : ∃ g : Fin Bs.r → PowerSeries O, (x : W.DD T) = ∑ k, framepf_ι π' (c - 1) (g k) • Bs.b k
  then Classical.choose h else 0

include hπ0 hR2 in
theorem framepf_gco_spec (x : ↥(NcS W T (c - 1))) :
    (x : W.DD T) = ∑ k, framepf_ι π' (c - 1) (framepf_gco Bs π' c x k) • Bs.b k := by
  have h := framepf_coord Bs π' (c - 1) hπ0 hR2 x.2
  unfold framepf_gco
  rw [dite_eq_left h]
  exact Classical.choose_spec h

include hπ0 hΔπ hR2 γ0 in
theorem framepf_gco_eq (x : ↥(NcS W T (c - 1))) (g : Fin Bs.r → PowerSeries O)
    (hg : (x : W.DD T) = ∑ k, framepf_ι π' (c - 1) (g k) • Bs.b k) : framepf_gco Bs π' c x = g :=
  framepf_coord_uniq Bs π' (c - 1) hπ0 hΔπ hR2 γ0
    ((framepf_gco_spec Bs π' c hπ0 hR2 x).symm.trans hg)

include hπ0 in
theorem framepf_ι_C_mul (o : O) (g : PowerSeries O) :
    framepf_ι π' (c - 1) (PowerSeries.C o * g) = algebraMap O (LetA O n) o * framepf_ι π' (c - 1) g := by
  rw [framepf_ι_mul π' (c - 1) (hπ0 _), framepf_ι_C π' (c - 1) (hπ0 _), mul_comm (letE (c - 1)),
    mul_assoc, framepf_letE_ι π' (c - 1) hπ0]

def framepf_coordL : ↥(NcS W T (c - 1)) →ₗ[O] (Fin Bs.r → O) where
  toFun x := fun k => PowerSeries.constantCoeff (framepf_gco Bs π' c x k)
  map_add' x y := by
    have e : framepf_gco Bs π' c (x + y) = framepf_gco Bs π' c x + framepf_gco Bs π' c y := by
      apply framepf_gco_eq Bs π' c hπ0 hΔπ hR2 γ0
      rw [Submodule.coe_add, framepf_gco_spec Bs π' c hπ0 hR2 x, framepf_gco_spec Bs π' c hπ0 hR2 y,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.add_apply, framepf_ι_add π' (c - 1) (hπ0 _), add_smul]
    funext k
    rw [e, Pi.add_apply, map_add (f := _)]
    rfl
  map_smul' o x := by
    have e : framepf_gco Bs π' c (o • x) = fun k => PowerSeries.C o * framepf_gco Bs π' c x k := by
      apply framepf_gco_eq Bs π' c hπ0 hΔπ hR2 γ0
      rw [Submodule.coe_smul, framepf_gco_spec Bs π' c hπ0 hR2 x, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [framepf_ι_C_mul π' c hπ0, mul_smul, algebraMap_smul]
    funext k
    rw [e, map_mul, PowerSeries.constantCoeff_C]
    rfl

theorem framepf_coordL_apply (x : ↥(NcS W T (c - 1))) (k : Fin Bs.r) :
    framepf_coordL Bs π' c hπ0 hΔπ hR2 γ0 x k = PowerSeries.constantCoeff (framepf_gco Bs π' c x k) := rfl

variable (hu : IsUnit (algebraMap (LetA O n) W.EE π'))


include hπ0 hΔπ hR2 γ0 hu in
theorem framepf_coordL_ker (x : ↥(NcS W T (c - 1))) :
    framepf_coordL Bs π' c hπ0 hΔπ hR2 γ0 x = 0 ↔ (x : W.DD T) ∈ PiNS W T π' 1 := by
  have hx := framepf_gco_spec Bs π' c hπ0 hR2 x
  have hxc := (mem_NcS W T (c - 1) x).1 x.2
  constructor
  · intro h0
    have hX : ∀ k, ∃ hk : PowerSeries O, framepf_gco Bs π' c x k = PowerSeries.X * hk := by
      intro k
      have := congrFun h0 k
      rw [framepf_coordL_apply] at this
      exact PowerSeries.X_dvd_iff.2 this
    choose hk hhk using hX
    rw [mem_PiNS]
    refine ⟨⟨∑ k, framepf_ι π' (c - 1) (hk k) • Bs.b k,
      Submodule.sum_mem _ fun k _ => (W.N T).smul_mem _ (Bs.mem k).1, ?_⟩, hxc.2.1⟩
    rw [pow_one, hx, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hhk k, smul_smul, framepf_ι_mul π' (c - 1) (hπ0 _), framepf_ι_X π' (c - 1) (hπ0 _),
      mul_comm (letE (c - 1)) π', mul_assoc, framepf_letE_ι π' (c - 1) hπ0]
  · intro h
    obtain ⟨⟨d, hdN, hd⟩, -⟩ := (mem_PiNS W T π' 1 _).1 h
    rw [pow_one] at hd
    have hdc : d ∈ NcS W T (c - 1) := by
      rw [mem_NcS]
      refine ⟨hdN, fun δ hδ => ?_, ?_⟩
      · rw [← sub_eq_zero]
        apply gradNPf_tf W T π' hu
        rw [smul_sub, ← hΔπ δ hδ, ← gradNPf_γD_smul, hΔπ δ hδ, hd, hxc.2.1 δ hδ, sub_self]
      · rw [← sub_eq_zero]
        apply gradNPf_tf W T π' hu
        rw [smul_sub, smul_smul, mul_comm, ← smul_smul, hd, hxc.2.2, sub_self]
    have hdd := framepf_gco_spec Bs π' c hπ0 hR2 ⟨d, hdc⟩
    have e : framepf_gco Bs π' c x = fun k => PowerSeries.X * framepf_gco Bs π' c ⟨d, hdc⟩ k := by
      apply framepf_gco_eq Bs π' c hπ0 hΔπ hR2 γ0
      rw [← hd]
      conv_lhs => rw [show d = ((⟨d, hdc⟩ : ↥(NcS W T (c - 1))) : W.DD T) from rfl, hdd]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, framepf_ι_mul π' (c - 1) (hπ0 _), framepf_ι_X π' (c - 1) (hπ0 _),
        mul_comm (letE (c - 1)) π', mul_assoc, framepf_letE_ι π' (c - 1) hπ0]
    funext k
    rw [framepf_coordL_apply, e]
    simp

include hπ0 hΔπ hR2 γ0 in
theorem framepf_coordL_surj : Function.Surjective (framepf_coordL Bs π' c hπ0 hΔπ hR2 γ0) := by
  intro o
  have hmem : ∑ k, framepf_ι π' (c - 1) (PowerSeries.C (o k)) • Bs.b k ∈ NcS W T (c - 1) := by
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [framepf_ι_C π' (c - 1) (hπ0 _), mul_comm, mul_smul, algebraMap_smul]
    exact (NcS W T (c - 1)).smul_mem _ (framepf_letE_mem Bs (c - 1) k)
  refine ⟨⟨_, hmem⟩, ?_⟩
  have e := framepf_gco_eq Bs π' c hπ0 hΔπ hR2 γ0 ⟨_, hmem⟩ (fun k => PowerSeries.C (o k)) rfl
  funext k
  rw [framepf_coordL_apply, e, PowerSeries.constantCoeff_C]

def framepf_Lbas : LcQ W T π' c ≃ₗ[O] (Fin Bs.r → O) :=
  (Submodule.quotEquivOfEq _ _ (by
    ext x
    rw [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_ker,
      framepf_coordL_ker Bs π' c hπ0 hΔπ hR2 γ0 hu])).trans
    (LinearMap.quotKerEquivOfSurjective _ (framepf_coordL_surj Bs π' c hπ0 hΔπ hR2 γ0))

theorem framepf_Lbas_mk (x : ↥(NcS W T (c - 1))) :
    framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu (Submodule.Quotient.mk x) =
      framepf_coordL Bs π' c hπ0 hΔπ hR2 γ0 x := rfl

def framepf_hh (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) : LcQ W T π' c →ₗ[O] W.DD T :=
  (Fintype.linearCombination O (fun k => framepf_vec Bs π' (c - 1) H k)).comp
    (framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu).toLinearMap

end Local

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfC
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Exp

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem FilC_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) :
    Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (a + 1) ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a := by
  unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
  exact sup_le_sup_right (ExtPf.extPf_fildR_succ_le PD T.ρ τ a) _

theorem FilC_anti (τ : K →ₐ[Qp] LL) : Antitone fun a => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a :=
  antitone_int_of_succ_le (fun a => FilC_succ_le T τ a)

theorem FilC_mono_shift (τ : K →ₐ[Qp] LL) (b : ℤ) :
    Monotone fun i : ℤ => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (b - i) :=
  fun i j hij => FilC_anti T τ (by omega : b - j ≤ b - i)

theorem FilC_top (τ : K →ₐ[Qp] LL) (hj : JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (b : ℤ) :
    Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ b ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-(h' : ℤ)) := by
  rcases le_or_gt (-(h' : ℤ)) b with hb | hb
  · exact FilC_anti T τ hb
  · have key : ∀ d : ℕ, FildR PD T.ρ τ (-(h' : ℤ) - (d : ℤ)) = FildR PD T.ρ τ (-(h' : ℤ)) := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        rw [← ih]
        have hnj : ¬ IsJumpV PD T.ρ τ (-(h' : ℤ) - ((d + 1 : ℕ) : ℤ)) := fun hJ => by
          have := (hj _ hJ).1
          push_cast at this
          omega
        unfold IsJumpV at hnj
        rw [not_not] at hnj
        have e : -(h' : ℤ) - ((d + 1 : ℕ) : ℤ) + 1 = -(h' : ℤ) - (d : ℤ) := by push_cast; ring
        rw [e] at hnj
        exact hnj.symm
    have := key ((-(h' : ℤ) - b).toNat)
    rw [show -(h' : ℤ) - (((-(h' : ℤ) - b).toNat : ℕ) : ℤ) = b by omega] at this
    unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
    rw [this]

include W in
theorem p_ne_zero : (PD.p : LL) ≠ 0 := by
  intro h
  have := W.v_l
  rw [h, AddValuation.map_zero] at this
  exact WithTop.top_ne_coe this

theorem pow_vanish (g : PowerSeries LL) (hg : PowerSeries.constantCoeff g = 0) (m : ℕ)
    (a : PowerSeries LL) : ∀ j < m, PowerSeries.coeff j (g ^ m * a) = 0 := by
  intro j hj
  have hX : (PowerSeries.X : PowerSeries LL) ∣ g := PowerSeries.X_dvd_iff.mpr hg
  obtain ⟨h, hh⟩ := pow_dvd_pow_of_dvd hX m
  rw [hh, mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

theorem pow_vanish' (g : PowerSeries LL) (hg : PowerSeries.constantCoeff g = 0) (m : ℕ) :
    ∀ j < m, PowerSeries.coeff j (g ^ m) = 0 := by
  intro j hj
  simpa using pow_vanish g hg m 1 j hj

variable {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop}

theorem levN_fil (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    (x : ↥(W.N T)) (k : ℤ) :
    W.levN T c ζ x k ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊓ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-k) := by
  rw [← levN_letE]
  exact (hp4.2 c ζ τ hPt).2.1 x k

theorem ιDi_le_top (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    (hj : JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) :
    Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-(h' : ℤ)) := by
  rw [← (hp4.2 c ζ τ hPt).1.2]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, k, hk, rfl⟩
  exact FilC_top T h' τ hj _ (Submodule.mem_inf.1 (levN_fil W T c hp4 hPt ⟨_, hk⟩ k)).2

theorem valAt_mem (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    {x : W.DD T} (hx : x ∈ W.N T) : valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c := by
  classical
  unfold valAt
  split_ifs with h
  · exact Submodule.smul_mem _ _ ((hp4.2 c ζ τ hPt).1.1 ⟨x, hx⟩ _ (Nat.find_spec h) _).1
  · exact Submodule.zero_mem _

theorem expS_mem (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ) {m : ℕ}
    (a : Fin m → LetA O n) (y : Fin m → W.DD T) (hy : ∀ j, y j ∈ W.N T) (i : ℤ) :
    expS W T c ζ a y i ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c := by
  unfold expS serC
  refine Submodule.sum_mem _ fun j _ => ?_
  split_ifs
  · exact Submodule.smul_mem _ _ (valAt_mem W T c hp4 hPt (hy j))
  · exact Submodule.zero_mem _

theorem levE_zero (hs : W.s = 1) {w w' : LetA O n} (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    (ζ : LL) (hζ : ζ ^ PD.p = 1) (hζ1 : ζ ≠ 1) :
    PowerSeries.constantCoeff (W.lev c ζ Eπ) = 0 := by
  have h0 := (levQ_pt W hs c ζ hζ hζ1).1
  have hw : PowerSeries.constantCoeff (W.lev c ζ w') * PowerSeries.constantCoeff (W.lev c ζ w) = 1 := by
    rw [← map_mul, ← map_mul, hww, map_one, map_one]
  rw [hQ, map_mul, map_mul] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · rw [h, mul_zero] at hw
    exact absurd hw zero_ne_one
  · exact h

end Exp

end Formalism.MainNotions.N.Ln34.ModelFPf

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UnivLinkPf
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules Formalism.MainNotions.N.Ln34.UnivLinkPf

theorem univLinkPf_deep_sub {up : Bool} {bτ S η h' : ℕ} (hb : η < bτ) (hS : bτ + S ≤ h') :
    deep up bτ S ∪ Set.Icc (-(η : ℤ)) η ⊆ Set.Icc (-(h' : ℤ)) h' := by
  intro a ha
  rcases ha with ha | ⟨h1, h2⟩
  · unfold deep at ha
    split_ifs at ha
    · obtain ⟨h1, h2⟩ := ha
      exact ⟨by omega, by omega⟩
    · obtain ⟨h1, h2⟩ := ha
      exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩


set_option maxHeartbeats 1000000 in
theorem univlink_pf : UnivLinkStep := by
  intro D HW Fo hA hd hR hC hH hMF hU1 hk hU2 hDn hUp hMx
  intro l _ hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b hN c
  obtain ⟨hc₁, hc₂, -, hJ₁, hJ₂, hηb, hbS, hh', -, hposition⟩ := id hN
  have hj₁ : ∀ τ, JumpsInV ((D.loc l).PD K) T₁.ρ τ (Set.Icc (-(h' : ℤ)) h') :=
    fun τ a ha => univLinkPf_deep_sub (hηb τ) (hbS τ) (hJ₁ τ a ha)
  have hj₂ : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h') :=
    fun τ a ha => univLinkPf_deep_sub (hηb τ) (hbS τ) (hJ₂ τ a ha)
  have hs : 1 ≤ sK l K := by
    have hdv := hd l hl K LL hG
    have hlp : l.Prime := Fact.out
    have h2 := hlp.two_le
    have hpos : 0 < l - 1 := by omega
    have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_dvd_iff] at hdv
      omega
    exact Nat.div_pos (Nat.le_of_dvd hpos hdv) he
  have hM : 1 ≤ MK l K h' := by
    have h4 : (0 : ℝ) < 4 * (h' : ℝ) := by
      have : (1 : ℝ) ≤ h' := by exact_mod_cast hh'
      linarith
    have hs' : (0 : ℝ) < (sK l K : ℝ) := by exact_mod_cast hs
    exact Nat.ceil_pos.2 (div_pos h4 hs')
  obtain ⟨α, β, hfr⟩ := hH l hl K LL hG π' E hp9 h' hh' c
  have hU3 : ThirdPropositionSlot ((HW l).W K 1 LL hG) F (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h'
      (MK l K h') S up b c (rhoA l (eK K) h' + max (2 * sigA l (sK l K) h') (ycA l h' η)) α := by
    rcases hposition with h2 | hsl
    · exact hMx l hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b c α β hfr hN h2
    · by_cases hex : ∃ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c ∧ up τ = true
      · obtain ⟨τ₀, hτ₀, hu₀⟩ := hex
        exact universal_lift_mono_exponent _ F (hUp l hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b c α β hfr hN
          fun τ hτ => (hsl τ τ₀ (hτ.trans hτ₀.symm)).trans hu₀) _
      · refine universal_lift_mono_exponent _ F (hDn l hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b c α β hfr hN
          fun τ hτ => ?_) _
        cases h : up τ
        · rfl
        · exact absurd ⟨τ, hτ, h⟩ hex
  obtain ⟨s₀, hcard, hsub, hmain⟩ := univLinkPf_local ((HW l).W K 1 LL hG) F hc₁ hc₂
    ((hA l K 1 LL hG).2.1 (fun h2 => absurd (((D.loc l).PD_p K).symm.trans h2) hl)) (hfr.1 T₂ hc₂ hj₂).2.2.2.1
    (hMF l hl K LL hG π' E hp9 h' hh' c α β hfr T₂ hc₂ hj₂) hM
    (hR l hl K LL hG π' E hp9 T₁ h' hh' hc₁ hj₁ c) (hR l hl K LL hG π' E hp9 T₂ h' hh' hc₂ hj₂ c)
    (hC l hl K LL hG π' E hp9 T₁ h' hh' hc₁ hj₁ c) (hC l hl K LL hG π' E hp9 T₂ h' hh' hc₂ hj₂ c)
    (hk l hl K LL hG π' E hp9 h' S up b c (fun τ => by have := hηb τ; omega) hbS)
    (hU1 l hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b c α β hfr) hN
    (hU2 l hl K LL hG π' E hp9 T₂ h' hh' hc₂ hj₂ c) hU3
  refine ⟨s₀, hcard, hsub, fun x hx => ?_⟩
  have h := hmain x hx
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  rw [hpl] at h
  have hexp : sigA l (sK l K) h' + y2K l K h' S η = sigA l (sK l K) h' +
      (2 * sigA l (sK l K) h' + kapA l (eK K) h' S +
        (rhoA l (eK K) h' + max (2 * sigA l (sK l K) h') (ycA l h' η))) := by
    unfold y2K; ring
  rw [hexp, ← Nat.cast_smul_eq_nsmul ↥(OL LL), Nat.cast_pow]
  exact h

end Formalism.MainNotions.N.Ln34

end
end

