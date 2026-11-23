module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0028
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0025
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0026
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0021
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.NinLamPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobPiNPf

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.RankLinkProof
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.RankLink

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem toLA_range_le (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n)
    (S : Submodule O (LcQ W T π' c)) :
    LinearMap.range (toLA W T π' c S) ≤ LinearMap.range (toLA W T π' c ⊤) := by
  have e : toLA W T π' c S =
      toLA W T π' c ⊤ ∘ₗ TensorProduct.map LinearMap.id (Submodule.inclusion le_top) := by
    apply TensorProduct.ext'
    intro x s
    simp [toLA, TensorProduct.map_tmul]
  rw [e]
  exact LinearMap.range_comp_le_range _ _

theorem lamLA_le (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)
    (S : Submodule O (LcQ W T π' c)) : LamLA W T π' Eπ h' c S ≤ LamLA W T π' Eπ h' c ⊤ := by
  unfold LamLA
  exact Submodule.comap_mono (toLA_range_le W T π' c S)

theorem invL_le (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    InvL W T Pt π' Eπ h' c S ≤ LamLA W T π' Eπ h' c ⊤ := by
  unfold InvL
  exact le_trans inf_le_left (lamLA_le W T π' Eπ h' c S)

def iota (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    IIrest W T Pt π' Eπ h' c S →ₗ[O] Formalism.MainNotions.N.Ln34.QL W T Pt π' Eπ h' c :=
  Submodule.mapQ _ _ (Submodule.inclusion (invL_le W T Pt π' Eπ h' c S)) (fun x hx => by
    simpa [Submodule.mem_comap] using hx)

theorem iota_inj (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    Function.Injective (iota W T Pt π' Eπ h' c S) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [LinearMap.mem_ker] at hy
  unfold iota at hy
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  simpa [Submodule.mem_comap] using hy

theorem rank_link_of_model [IsDomain O] [IsPrincipalIdealRing O] (T : LocLat G Qp LL O)
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)
    (hQ : ModelQ W T Pt π' Eπ h' c) (hR : SecondRankCount W T Pt π' Eπ h' c) : SecondPropositionFree W T Pt π' Eπ h' c := by
  intro S
  obtain ⟨hfin, htf⟩ := hQ
  have hinj := iota_inj W T Pt π' Eπ h' c S
  haveI : Module.Finite O (Formalism.MainNotions.N.Ln34.QL W T Pt π' Eπ h' c) := hfin
  haveI : IsNoetherian O (Formalism.MainNotions.N.Ln34.QL W T Pt π' Eπ h' c) :=
    isNoetherian_of_isNoetherianRing_of_finite O _
  haveI hfinI : Module.Finite O (IIrest W T Pt π' Eπ h' c S) :=
    Module.Finite.of_injective (iota W T Pt π' Eπ h' c S) hinj
  haveI : NoZeroSMulDivisors O (Formalism.MainNotions.N.Ln34.QL W T Pt π' Eπ h' c) := by
    refine ⟨fun {a q} h => ?_⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr (htf a q ha h)
  haveI : NoZeroSMulDivisors O (IIrest W T Pt π' Eπ h' c S) :=
    Function.Injective.noZeroSMulDivisors _ hinj (map_zero _) (fun a x => map_smul _ a x)
  exact ⟨hfinI, Module.free_of_finite_type_torsion_free', hR S⟩

end Local

set_option maxHeartbeats 1000000 in
theorem rank_link_holds : Formalism.MainNotions.N.Ln34.SecondPropositionOfRank := by
  intro D HW hM hR l _ hl K LL hG π' E hp T h' hh hC hJ c
  haveI := Formalism.MainNotions.N.Ln34.GenPf.isDVR (D.loc l) LL
  exact rank_link_of_model _ T _ π' _ h' c (hM l hl K LL hG π' E hp h' hh T hC hJ c)
    (hR l hl K LL hG π' E hp T h' hh hC hJ c)

end Formalism.MainNotions.N.Ln34.RankLink

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3upPfFilCAnti
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem u3upPf_FilC_anti (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) {a a' : ℤ} (h : a' ≤ a) :
    Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a' := by
  have hs : ∀ k : ℤ, FildR PD T.ρ τ (k + 1) ≤ FildR PD T.ρ τ k := by
    intro k
    refine inf_le_inf_left _ ?_
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul u w => exact ⟨u ⊗ₜ ⟨(w : BdR), PD.Fil_anti k w.2⟩, rfl⟩
    | add z z' hz hz' => rw [map_add (f := _)]; exact Submodule.add_mem _ hz hz'
  have hA : Antitone fun k => FildR PD T.ρ τ k := antitone_int_of_succ_le hs
  unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
  exact sup_le_sup_right (hA h) _

theorem u3upPf_memNL (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' S : ℕ) (up : (K →ₐ[Qp] LL) → Bool) (b : (K →ₐ[Qp] LL) → ℕ) (c : ZMod n)
    (hPt : ∀ ζ τ, Pt c ζ τ → Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c)
    (hup : ∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c → up τ = true) (f : W.EE)
    (hf : IsCoord W Pt π' Eπ h' S up b c f) (x : W.DD T) (hx : x ∈ NcS W T (c - 1))
    (hFil : ∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c → up τ = true → x ∈ FilL W T Pt c τ (b τ)) :
    f ⊗ₜ mkL W T π' c x hx ∈ NL W T Pt π' Eπ h' c := by
  obtain ⟨a, ha, hea, hΛ, hup0, -, -⟩ := hf
  apply Submodule.subset_span
  refine ⟨1, fun _ => ⟨a, ha⟩, fun _ => x, ⟨fun _ => hx, ?_⟩, ?_⟩
  · rw [Fin.sum_univ_one]
    show TensorProduct.map (LinearMap.mulLeft O (algebraMap (LetA O n) W.EE (Eπ ^ h'))) LinearMap.id
        (f ⊗ₜ mkL W T π' c x hx) = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ mkL W T π' c x hx
    rw [TensorProduct.map_tmul, LinearMap.mulLeft_apply, LinearMap.id_apply, hΛ, hea]
  · intro τ ζ hpt i
    have hO := hPt ζ τ hpt
    have hu := hup τ hO
    have hv : valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (b τ) := hFil τ hO hu ζ hpt
    show (∑ j : Fin 1, serC (W.lev c ζ a) (valAt W T c ζ x) i) ∈ _
    rw [Fin.sum_univ_one]
    unfold serC
    split_ifs with hi
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      simp only [Int.toNat_natCast]
      by_cases hlt : k + b τ < h'
      · rw [hup0 τ ζ hpt hu k hlt, zero_smul]
        exact Submodule.zero_mem _
      · apply Submodule.smul_mem
        refine u3upPf_FilC_anti T τ ?_ hv
        push_neg at hlt
        omega
    · exact Submodule.zero_mem _

theorem u3upPf_PiNS_one (T : LocLat G Qp LL O) (π' : LetA O n) {M : ℕ} (hM : 1 ≤ M) {z : W.DD T}
    (hz : z ∈ PiNS W T π' M) : z ∈ PiNS W T π' 1 := by
  obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.1 hz
  refine Submodule.mem_inf.2 ⟨?_, hz2⟩
  rw [Submodule.restrictScalars_mem] at hz1 ⊢
  unfold Formalism.MainNotions.DeltaInvariantLattices.aN at hz1 ⊢
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz1
  refine Submodule.mem_map.2 ⟨π' ^ (M - 1) • w, (W.N T).smul_mem _ hw, ?_⟩
  simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply]
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hM]

theorem u3upPf_lift {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' M ρ : ℕ) (c : ZMod n)
    (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c)
    (hMF : ModelF W T₂ Pt π' Eπ h' M c α β) (hM : 1 ≤ M) (hW : WKill W F ρ)
    (hNL : NinLam W T₁ Eπ h') (hG1 : GamPi W T₁ π') (hG2 : GamPi W T₂ π')
    (x : LA W T₂ π' c) (hx : x ∈ LamLA W T₂ π' Eπ h' c ⊤) (hxN : x ∈ NL W T₂ Pt π' Eπ h' c)
    (y : W.DD T₂) (hy : y ∈ LamPS W T₂ Eπ h' c)
    (hα : α T₂ ⟨x, hx⟩ = mkP W T₂ π' Eπ h' M c y hy) : LiftsBy W F π' Eπ h' ρ c y := by
  obtain ⟨n₂, hn₂, hn₂N, hα₂⟩ := hMF.1 x hx hxN
  have hd : y - n₂ ∈ PiNS W T₂ π' M := by
    refine (hMF.2.2.1 M hM le_rfl).1 0 (Submodule.zero_mem _) (y - n₂)
      (Submodule.sub_mem _ hy hn₂) ?_ (Submodule.zero_mem _)
    have h0 : (⟨0, Submodule.zero_mem _⟩ : ↥(LamLA W T₂ π' Eπ h' c ⊤)) = 0 := rfl
    rw [h0, map_zero]
    symm
    show Submodule.Quotient.mk ((⟨y, hy⟩ : ↥(LamPS W T₂ Eπ h' c)) - ⟨n₂, hn₂⟩) =
      (0 : QLamP W T₂ π' Eπ h' M c)
    rw [Submodule.Quotient.mk_sub, sub_eq_zero]
    exact hα.symm.trans hα₂
  have hyN : y ∈ NcS W T₂ c := by
    obtain ⟨-, hΔ, hl⟩ := (mem_LamPS W T₂ Eπ h' c y).1 hy
    refine (mem_NcS W T₂ c y).2 ⟨?_, hΔ, hl⟩
    have h1 := PiNS_le_N W T₂ π' M hd
    have h2 := ((mem_NcS W T₂ c n₂).1 hn₂N).1
    have h3 := Submodule.add_mem _ h1 h2
    rwa [sub_add_cancel] at h3
  obtain ⟨n₁, hn₁, hF⟩ := hW c n₂ hn₂N
  refine ⟨(mem_InvS W T₂ π' Eπ h' 1 c y).2 ⟨hy, (Submodule.mem_inf.1 (hG2 c y hyN)).1⟩, n₁,
    (mem_InvS W T₁ π' Eπ h' 1 c n₁).2 ⟨hNL c hn₁, (Submodule.mem_inf.1 (hG1 c n₁ hn₁)).1⟩, ?_⟩
  rw [hF, ← smul_sub]
  exact Submodule.smul_mem _ _ (u3upPf_PiNS_one W T₂ π' hM hd)

end Local

theorem u3upPf_pt_over (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
    (hG : Good K 1 LL) (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) : Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c := by
  obtain ⟨τs, ⟨hemb, -⟩, hres⟩ := hpt
  apply AlgHom.ext
  intro z
  have hzK : (z : Om l) ∈ Ks K 1 := (le_sup_left : K0 K ≤ Ks K 1) z.2
  rw [AlgHom.comp_apply, hres (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 z) ⟨z, hzK⟩ rfl]
  exact hemb z ⟨z, hzK⟩ rfl

theorem u3upPf_MK_pos {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL) (h' : ℕ)
    (hh' : 1 ≤ h') : 1 ≤ MK l K h' := by
  have hs := frobpin_sK_pos hl K LL hG
  have h4 : (0 : ℝ) < 4 * (h' : ℝ) := by
    have : (1 : ℝ) ≤ h' := by exact_mod_cast hh'
    linarith
  have hs' : (0 : ℝ) < (sK l K : ℝ) := by exact_mod_cast hs
  exact Nat.ceil_pos.2 (div_pos h4 hs')

theorem u3upPf_ofR (D : D7) (HW : HWOf D.loc) (hMF : modelFR D HW) (hW : wKillR D HW)
    (hNL : ninLamR D HW) (hGP : gamPiR D HW) : UpSlotProposition D HW := by
  intro l _ hl K LL hG π' E hπ T₁ T₂ F S η m h' up b c α β hfr hN hall
  intro f hf x hx hFil h1 y hy hα
  obtain ⟨hc1, hc2, hon, hj1, hj2, hηb, hbS, hh', -, -⟩ := hN
  have hjI : ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
      (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) →
      ∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h') := by
    intro T hj τ a ha
    have hd := hj τ a ha
    have hb := hbS τ
    have hη := hηb τ
    rw [Set.mem_Icc]
    rcases hd with hd | hd
    · unfold deep at hd
      split_ifs at hd <;> (rw [Set.mem_Icc] at hd; constructor <;> omega)
    · rw [Set.mem_Icc] at hd
      constructor <;> omega
  have hM := u3upPf_MK_pos hl K LL hG h' hh'
  have hMF2 := hMF l hl K LL hG π' E hπ h' hh' c α β hfr T₂ hc2 (hjI T₂ hj2)
  have hW' := hW l hl K LL hG π' E hπ T₁ T₂ F h' hc1 hc2 hon (hjI T₁ hj1)
  have hNL1 := hNL l hl K LL hG π' E hπ T₁ h' hc1 (hjI T₁ hj1)
  have hG1 := hGP l hl K LL hG π' E hπ T₁ hc1
  have hG2 := hGP l hl K LL hG π' E hπ T₂ hc2
  have hxN := u3upPf_memNL _ T₂ _ π' _ h' S up b c (fun ζ τ hpt => u3upPf_pt_over D HW hG c ζ τ hpt)
    hall f hf x hx hFil
  exact u3upPf_lift _ F _ π' _ h' _ _ c α β hMF2 hM hW' hNL1 hG1 hG2 _ h1 hxN y hy hα

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UnivLinkPfA
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.UnivLinkPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem univLinkPf_PiNS_anti (T : LocLat G Qp LL O) (π' : LetA O n) {j k : ℕ} (h : j ≤ k)
    {x : W.DD T} (hx : x ∈ PiNS W T π' k) : x ∈ PiNS W T π' j := by
  rw [PiNS, Submodule.mem_inf, Submodule.restrictScalars_mem, Formalism.MainNotions.DeltaInvariantLattices.aN, Submodule.mem_map] at hx ⊢
  obtain ⟨⟨y, hy, rfl⟩, hx2⟩ := hx
  refine ⟨⟨π' ^ (k - j) • y, Submodule.smul_mem _ _ hy, ?_⟩, hx2⟩
  simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← pow_add, Nat.add_sub_cancel' h]

theorem univLinkPf_InvS_anti (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)
    {j k : ℕ} (h : j ≤ k) {x : W.DD T} (hx : x ∈ InvS W T π' Eπ h' k c) : x ∈ InvS W T π' Eπ h' j c := by
  rw [InvS, Submodule.mem_inf, Submodule.mem_comap] at hx ⊢
  exact ⟨hx.1, univLinkPf_PiNS_anti W T π' h hx.2⟩

theorem univLinkPf_cocycle {T : LocLat G Qp LL O} {y z : W.DD T} (h : (y, z) ∈ W.wachCocyclesDelta T) :
    W.γD T W.gamK y - y = W.φD T z - z := by
  have h1 := ((Formalism.MainNotions.LiftingTheory.lifta_mem_Z1DΔ W T y z).mp h).1
  try simp only [herrCocycles, Set.mem_setOf_eq, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at h1
  simp only [LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply] at h1
  rw [← sub_eq_zero, sub_eq_add_neg]
  exact h1

theorem univLinkPf_cocycleΔ {T : LocLat G Qp LL O} {y z : W.DD T} (h : (y, z) ∈ W.wachCocyclesDelta T) :
    ∀ δ ∈ W.DelF, W.γD T δ y = y ∧ W.γD T δ z = z := ((Formalism.MainNotions.LiftingTheory.lifta_mem_Z1DΔ W T y z).mp h).2

theorem univLinkPf_mem_Z1DΔ {T : LocLat G Qp LL O} (y z : W.DD T) (hy : ∀ δ ∈ W.DelF, W.γD T δ y = y)
    (hz : ∀ δ ∈ W.DelF, W.γD T δ z = z) (h : W.γD T W.gamK y - y = W.φD T z - z) :
    (y, z) ∈ W.wachCocyclesDelta T := by
  refine (Formalism.MainNotions.LiftingTheory.lifta_mem_Z1DΔ W T y z).mpr ⟨?_, fun δ hδ => ⟨hy δ hδ, hz δ hδ⟩⟩
  try simp only [herrCocycles, Set.mem_setOf_eq, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
  simp only [LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply]
  rw [← sub_eq_add_neg, sub_eq_zero]
  exact h

section Map

variable {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)

theorem univLinkPf_map_DelS {x : W.DD T₁} (hx : ∀ δ ∈ W.DelF, W.γD T₁ δ x = x) :
    ∀ δ ∈ W.DelF, W.γD T₂ δ (W.map F x) = W.map F x := by
  intro δ hδ
  rw [← W.map_γ F δ x, hx δ hδ]

theorem univLinkPf_map_PiNS (h1 : IsCrys PD T₁.ρ) (h2 : IsCrys PD T₂.ρ) (π' : LetA O n) (k : ℕ)
    {x : W.DD T₁} (hx : x ∈ PiNS W T₁ π' k) : W.map F x ∈ PiNS W T₂ π' k := by
  have hDel : ∀ {T : LocLat G Qp LL O} {x : W.DD T}, x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
    intro T x
    simp [DelS, Submodule.mem_iInf, sub_eq_zero]
  rw [PiNS, Submodule.mem_inf, Submodule.restrictScalars_mem, Formalism.MainNotions.DeltaInvariantLattices.aN, Submodule.mem_map] at hx ⊢
  obtain ⟨⟨y, hy, rfl⟩, hx2⟩ := hx
  refine ⟨⟨W.map F y, W.map_N F h1 h2 y hy, ?_⟩, hDel.mpr (univLinkPf_map_DelS W F (hDel.mp hx2))⟩
  simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply]
  exact ((Formalism.MainNotions.DeltaInvariantLattices.mapA W F).map_smul _ _).symm

theorem univLinkPf_map_φspan (h1 : IsCrys PD T₁.ρ) (h2 : IsCrys PD T₂.ρ) (c : ZMod n) {x : W.DD T₁}
    (hx : x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T₁ (W.Nl T₁ c)) : W.map F x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T₂ (W.Nl T₂ c) := by
  have hNl : ∀ y ∈ W.Nl T₁ c, W.map F y ∈ W.Nl T₂ c := by
    intro y hy
    unfold Formalism.BasicNotions.LocWach.Nl at hy ⊢
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    refine Submodule.mem_map.mpr ⟨W.map F z, W.map_N F h1 h2 z hz, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    exact ((Formalism.MainNotions.DeltaInvariantLattices.mapA W F).map_smul _ _).symm
  unfold Formalism.MainNotions.DeltaInvariantLattices.φspan at hx ⊢
  have hm : (Formalism.MainNotions.DeltaInvariantLattices.mapA W F) x ∈ Submodule.map (Formalism.MainNotions.DeltaInvariantLattices.mapA W F)
      (Submodule.span (LetA O n) (W.φD T₁ '' (W.Nl T₁ c : Set (W.DD T₁)))) := Submodule.mem_map_of_mem hx
  rw [Submodule.map_span] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨W.map F y, hNl y hy, (W.map_φ F y).symm⟩

theorem univLinkPf_map_LamPS (h1 : IsCrys PD T₁.ρ) (h2 : IsCrys PD T₂.ρ) (Eπ : LetA O n) (h' : ℕ)
    (c : ZMod n) {x : W.DD T₁} (hx : x ∈ LamPS W T₁ Eπ h' c) : W.map F x ∈ LamPS W T₂ Eπ h' c := by
  have hDel : ∀ {T : LocLat G Qp LL O} {x : W.DD T}, x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
    intro T x
    simp [DelS, Submodule.mem_iInf, sub_eq_zero]
  have hsm : ∀ (a : LetA O n) (y : W.DD T₁), W.map F (a • y) = a • W.map F y :=
    fun a y => (Formalism.MainNotions.DeltaInvariantLattices.mapA W F).map_smul a y
  rw [LamPS, Submodule.mem_inf, Submodule.mem_inf] at hx ⊢
  obtain ⟨⟨hA, hB⟩, hC⟩ := hx
  refine ⟨⟨?_, hDel.mpr (univLinkPf_map_DelS W F (hDel.mp hB))⟩, ?_⟩
  · rw [Submodule.restrictScalars_mem, Submodule.mem_comap] at hA ⊢
    have hφ := univLinkPf_map_φspan W F h1 h2 (c - 1) hA
    simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply] at hφ ⊢
    rw [hsm] at hφ
    exact hφ
  · rw [letS, LinearMap.mem_ker] at hC ⊢
    simp only [LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at hC ⊢
    rw [← hsm, ← map_sub, hC, map_zero]

theorem univLinkPf_map_InvS (h1 : IsCrys PD T₁.ρ) (h2 : IsCrys PD T₂.ρ) (π' Eπ : LetA O n) (h' k : ℕ)
    (c : ZMod n) {x : W.DD T₁} (hx : x ∈ InvS W T₁ π' Eπ h' k c) : W.map F x ∈ InvS W T₂ π' Eπ h' k c := by
  rw [InvS, Submodule.mem_inf, Submodule.mem_comap] at hx ⊢
  refine ⟨univLinkPf_map_LamPS W F h1 h2 Eπ h' c hx.1, ?_⟩
  have hP := univLinkPf_map_PiNS W F h1 h2 π' k hx.2
  simp only [LinearMap.sub_apply, LinearMap.id_apply] at hP ⊢
  rw [map_sub, W.map_γ] at hP
  exact hP

theorem univLinkPf_map_Z1DΔ {y z : W.DD T₁} (h : (y, z) ∈ W.wachCocyclesDelta T₁) :
    (W.map F y, W.map F z) ∈ W.wachCocyclesDelta T₂ := by
  have hc := univLinkPf_cocycle W h
  have hd := univLinkPf_cocycleΔ W h
  apply univLinkPf_mem_Z1DΔ W
  · exact univLinkPf_map_DelS W F (fun δ hδ => (hd δ hδ).1)
  · exact univLinkPf_map_DelS W F (fun δ hδ => (hd δ hδ).2)
  · rw [← W.map_γ, ← W.map_φ, ← map_sub, ← map_sub, hc]

end Map

section Frame

variable (T : LocLat G Qp LL O)

theorem univLinkPf_toLA_eq (π' : LetA O n) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    toLA W T π' c S = (toLA W T π' c ⊤).comp (TensorProduct.map LinearMap.id (Submodule.inclusion le_top)) := by
  unfold toLA
  rw [← TensorProduct.map_comp, LinearMap.comp_id, Submodule.subtype_comp_inclusion]

theorem univLinkPf_LamLA_le (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    LamLA W T π' Eπ h' c S ≤ LamLA W T π' Eπ h' c ⊤ := by
  unfold LamLA
  refine Submodule.comap_mono ?_
  rw [univLinkPf_toLA_eq W T π' c S]
  exact LinearMap.range_comp_le_range _ _

theorem univLinkPf_InvL_le (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' : ℕ)
    (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    InvL W T Pt π' Eπ h' c S ≤ InvL W T Pt π' Eπ h' c ⊤ := by
  unfold InvL
  exact inf_le_inf_right _ (univLinkPf_LamLA_le W T π' Eπ h' c S)

theorem univLinkPf_basis [StrongRankCondition O] (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c))
    [Module.Finite O (IIrest W T Pt π' Eπ h' c S)] [Module.Free O (IIrest W T Pt π' Eπ h' c S)] :
    ∃ xb : Fin (finrank O (IIrest W T Pt π' Eπ h' c S)) → ↥(InvL W T Pt π' Eπ h' c S),
      ∀ x : ↥(InvL W T Pt π' Eπ h' c S), ∃ o : Fin (finrank O (IIrest W T Pt π' Eπ h' c S)) → O,
        (x : LA W T π' c) - ∑ i, o i • (xb i : LA W T π' c) ∈ piNL W T Pt π' Eπ h' c 1 := by
  classical
  let b := Module.finBasis O (IIrest W T Pt π' Eπ h' c S)
  choose xb hxb using fun i => Submodule.Quotient.mk_surjective _ (b i)
  refine ⟨xb, fun x => ⟨fun i => b.repr (Submodule.Quotient.mk x) i, ?_⟩⟩
  have h : (Submodule.Quotient.mk x : IIrest W T Pt π' Eπ h' c S) =
      Submodule.Quotient.mk (∑ i, b.repr (Submodule.Quotient.mk x) i • xb i) := by
    rw [show (Submodule.Quotient.mk (∑ i, b.repr (Submodule.Quotient.mk x) i • xb i) :
        IIrest W T Pt π' Eπ h' c S) =
        Submodule.mkQ _ (∑ i, b.repr (Submodule.Quotient.mk x) i • xb i) from rfl]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Submodule.mkQ_apply, hxb]
    exact (b.sum_repr _).symm
  rw [Submodule.Quotient.eq] at h
  simpa using h

theorem univLinkPf_JP {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' M : ℕ}
    {c : ZMod n} {α : FrA W π' Eπ h' M c} {β : FrB W π' Eπ h' M c}
    (hMF : ModelF W T Pt π' Eπ h' M c α β) (hM : 1 ≤ M) (y : ↥(LamPS W T Eπ h' c))
    (hJ : Submodule.Quotient.mk y = (0 : QLamP W T π' Eπ h' M c)) : (y : W.DD T) ∈ PiNS W T π' M := by
  refine (hMF.2.2.1 M hM le_rfl).1 0 (Submodule.zero_mem _) y.1 y.2 ?_ (Submodule.zero_mem _)
  show α T 0 = _
  rw [map_zero]
  exact hJ.symm

theorem univLinkPf_transport {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' M : ℕ}
    {c : ZMod n} {α : FrA W π' Eπ h' M c} {β : FrB W π' Eπ h' M c}
    (hMF : ModelF W T Pt π' Eπ h' M c α β) (hM : 1 ≤ M) {k r : ℕ}
    (X : ↥(LamLA W T π' Eπ h' c ⊤)) (Y : ↥(LamPS W T Eπ h' c))
    (hX : α T X = Submodule.Quotient.mk Y)
    (Xj : Fin k → ↥(LamLA W T π' Eπ h' c ⊤)) (Yj : Fin k → ↥(LamPS W T Eπ h' c))
    (hXj : ∀ j, α T (Xj j) = Submodule.Quotient.mk (Yj j))
    (Xb : Fin r → ↥(LamLA W T π' Eπ h' c ⊤)) (Yb : Fin r → ↥(LamPS W T Eπ h' c))
    (hXb : ∀ i, α T (Xb i) = Submodule.Quotient.mk (Yb i)) (o : Fin r → O)
    (hrel : (X : LA W T π' c) - ∑ j, (Xj j : LA W T π' c) - ∑ i, o i • (Xb i : LA W T π' c) ∈
      piNL W T Pt π' Eπ h' c 1) :
    (Y : W.DD T) - ∑ j, (Yj j : W.DD T) - ∑ i, o i • (Yb i : W.DD T) ∈ PiNS W T π' 1 := by
  have h3 := (hMF.2.2.1 1 le_rfl hM).1
  have hαx : α T (X - ∑ j, Xj j - ∑ i, o i • Xb i) =
      Submodule.Quotient.mk (Y - ∑ j, Yj j - ∑ i, o i • Yb i) := by
    rw [show (Submodule.Quotient.mk (Y - ∑ j, Yj j - ∑ i, o i • Yb i) : QLamP W T π' Eπ h' M c) =
      Submodule.mkQ _ (Y - ∑ j, Yj j - ∑ i, o i • Yb i) from rfl]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smul, Submodule.mkQ_apply, hX, hXj, hXb]
  have hmem := h3 ((X - ∑ j, Xj j - ∑ i, o i • Xb i : ↥(LamLA W T π' Eπ h' c ⊤)) : LA W T π' c)
    (X - ∑ j, Xj j - ∑ i, o i • Xb i).2
    ((Y - ∑ j, Yj j - ∑ i, o i • Yb i : ↥(LamPS W T Eπ h' c)) : W.DD T)
    (Y - ∑ j, Yj j - ∑ i, o i • Yb i).2 hαx (by simpa using hrel)
  simpa using hmem

end Frame

end Local

end Formalism.MainNotions.N.Ln34.UnivLinkPf

end
end

