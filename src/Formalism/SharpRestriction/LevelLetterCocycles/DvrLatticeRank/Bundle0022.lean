module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0021
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0031
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfDMain
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfTNatCastUnit
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsUnramifiedStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0022
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3downPfFildRConst
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.KapPiPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfRec
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
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O)


include Ct in
theorem framepf_data' [IsDomain O] (hι : Function.Injective (algebraMap O LL)) (hT : IsCrys PD T.ρ)
    (hs : W.s = 1) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (c : ZMod n)
    (hprim : ∀ τ ζ, Pt c ζ τ → IsPrimitiveRoot ζ PD.p) (h4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    {e s' : ℕ} {π' : LetA O n} {Ep : ZMod n → Polynomial O} (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' Ep)
    (hs' : 1 ≤ s') (h' M σ : ℕ) (hM1 : 1 ≤ M) (hM : 4 * h' ≤ s' * M) (l : ℕ) (hl : PD.p = l)
    (hyp : Nonempty (FramepfBas W T) ∧ (∀ j, PowerSeries.constantCoeff (π' j) = 0) ∧
      (∀ δ ∈ W.DelF, W.γA δ π' = π') ∧
      (∀ a ∈ W.AΔ, ∃! f : ZMod n → PowerSeries O, ∀ j, a j = PowerSeries.subst (π' j) (f j)) ∧
      (∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0) ∧
      IsUnit (algebraMap (LetA O n) W.EE π') ∧
      (∀ y ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam y - y = π' • d) ∧ W.gamK = W.gam ∧
      ∃ Fs : PowerSeries O,
        W.γ₀ W.gam (π' (c - 1)) = PowerSeries.subst (π' (c - 1)) (PowerSeries.X * Fs) ∧
        PowerSeries.constantCoeff Fs = ((W.χΓ W.gam : Oˣ) : O) ^ s' ∧
        (∀ y : ℕ, 1 ≤ y → (((W.χΓ W.gam : Oˣ) : O) ^ s') ^ y ≠ 1) ∧
        ∃ aσ : O, (l : O) ^ σ = aσ * ∏ y ∈ Finset.Ico 1 M, ((((W.χΓ W.gam : Oˣ) : O) ^ s') ^ y - 1))
    (hB : ∀ (Bs : FramepfBas W T) hπ0 hΔπ hR2 γ0 hu,
      FramepfBack Bs π' c hπ0 hΔπ hR2 γ0 hu (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' M) :
    ∃ (hh : LcQ W T π' c →ₗ[O] W.DD T)
      (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c),
      (∀ x ∈ LamLA W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c ⊤, Ψ x ∈ LamPS W T (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c) ∧
      (∀ y ∈ LamPS W T (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c, Φ y ∈ LamLA W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c ⊤) ∧
      FramepfData W Pt π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' M σ c T hh Ψ Φ := by
  obtain ⟨⟨Bs⟩, hπ0, hΔπ, hR2, γ0, hu, hγN, hK, Fs, hFs, hF0, hne, aσ, haσ⟩ := hyp
  exact framepf_data Ct T hι hT hs Pt c hprim h4 hR hs' h' M σ hM1 hM hK
    Bs hπ0 hΔπ hR2 γ0 hu hγN Fs hFs hF0 hne aσ (by rw [hl]; exact haσ) (hB Bs hπ0 hΔπ hR2 γ0 hu)

end Local


set_option maxHeartbeats 1000000 in
theorem framepf_rec (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (h' : ℕ) (hh' : 1 ≤ h')
    (c : ZMod (finrank ℚ_[l] ↥(K0 K)))
    (hB : ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ →
      ∀ (Bs : FramepfBas ((HW l).W K 1 LL hG) T) hπ0 hΔπ hR2 γ0 hu,
        IsUnit (algebraMap _ ((HW l).W K 1 LL hG).EE (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) →
        Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ → ∀ u ∈ ((HW l).W K 1 LL hG).AΔ,
        ((HW l).W K 1 LL hG).φA π' ^ MK l K h' = π' ^ MK l K h' * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ (4 * h') * u →
        FramepfBack Bs π' c hπ0 hΔπ hR2 γ0 hu (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h')) :
    FrameA ((HW l).W K 1 LL hG) (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h')
      (sigA l (sK l K) h') c := by
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hK : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam := ((HW l).W K 1 LL hG).gamK_eq_one hs hp2
  have hs' := ramification_quotient_pos l hl K LL hG
  have hM : 4 * h' ≤ sK l K * MK l K h' := by
    have hsR : (0 : ℝ) < (sK l K : ℝ) := by exact_mod_cast hs'
    have hc : (4 * h' : ℝ) / (sK l K : ℝ) ≤ (MK l K h' : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hsR] at hc
    have h4 : ((4 * h' : ℕ) : ℝ) ≤ ((sK l K * MK l K h' : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h4
  have hM1 : 1 ≤ MK l K h' := by
    rcases Nat.eq_zero_or_pos (MK l K h') with h0 | h0
    · rw [h0, mul_zero] at hM
      omega
    · exact h0
  have hprim : ∀ τ ζ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → IsPrimitiveRoot ζ ((D.loc l).PD K).p := by
    intro τ ζ hpt
    rw [hpl]
    exact framepf_pt_prim D HW hG c ζ τ hpt
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  obtain ⟨u, huΔ, hφ⟩ := framepf_φπ hR hs h' _ hM
  obtain ⟨f, hfΔ, hf⟩ := framepf_γπ hR
  obtain ⟨t, htΔ, ht⟩ := framepf_γE hR hs ((HW l).W K 1 LL hG).gamK
  obtain ⟨t', ht'Δ, ht'⟩ := framepf_γE' hR hs ((HW l).W K 1 LL hG).gamK
  have huE := framepf_E_unit hR hs
  refine framepf_frameA _ _ π' _ h' _ _ c hK (framepf_π_unit hR) huE hR.1 u huΔ hφ hfΔ
    (by rw [hK]; exact hf) htΔ ht ht'Δ ht' fun T hT => ?_
  exact framepf_data' ((Cm l).C K 1 LL hG).tie T hι hT hs _ c hprim ((h1 l K 1 LL hG).2.2.2.1 T hT) hR
    hs' h' _ _ hM1 hM l hpl (framepf_hyps D HW F Cm h1 l hl K LL hG π' E hR T hT c h')
    fun Bs hπ0 hΔπ hR2 γ0 hu => hB T hT Bs hπ0 hΔπ hR2 γ0 hu huE (framepf_E_Δ hR) u huΔ hφ

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPf
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules Formalism.MainNotions.N.Ln34.ModelFPf

theorem modelflink_pf : ModelFLinkStep := by
  intro D HW F Cm CA CB CK hA hP l _ hl K LL hG π' E hπ h' hh' c α β hfr T hcry hjmp
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  obtain ⟨-, -, -, h4W, h5W, -⟩ := hA.1 l K 1 LL hG
  obtain ⟨h5a, h5b, -⟩ := h5W T (fun _ => h') (fun _ => h') hcry (fun τ _ _ => hjmp τ)
  obtain ⟨hπΔ, -, ⟨w0, hw0⟩, -, ⟨w, hw⟩, -, ⟨w2, hw2⟩, -⟩ := hπ
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl)
  have hQ : ((HW l).W K 1 LL hG).Q = (w : LetA _ _) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' := by
    rw [Q_eq_q _ hs]
    exact hw
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have hM : 1 ≤ MK l K h' := by
    refine Nat.one_le_ceil_iff.2 (div_pos ?_ ?_)
    · have : (1 : ℝ) ≤ h' := by exact_mod_cast hh'
      linarith
    · exact_mod_cast hsK
  have hEΔ : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ := by
    intro δ hδ
    funext i
    show ((HW l).W K 1 LL hG).γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply]
    exact congrArg (fun t => Polynomial.aeval t (E i)) (congrFun (hπΔ δ hδ) i)
  have hπu : IsUnit (algebraMap (LetA _ _) ((HW l).W K 1 LL hG).EE π') := by
    rw [hw0, map_mul, map_pow]
    exact (w0.isUnit.map _).mul (((HW l).W K 1 LL hG).EE_π.pow _)
  obtain ⟨u, hu, hγ⟩ := gam_unit ((HW l).W K 1 LL hG) π' E hsK w2 hw2 w0 hw0
  have hpO : (((D.loc l).PD K).p : ↥(OL LL)) ≠ 0 := fun h0 => by
    apply p_ne_zero ((HW l).W K 1 LL hG)
    rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1), h0, map_zero]
  have hnz := Eπ_nzd ((HW l).W K 1 LL hG) hw (q0_ne_two_and_ne_q_and_ne_d ((HW l).W K 1 LL hG) hpO)
  have huΔ := u_mem_AΔ ((HW l).W K 1 LL hG) hEΔ hnz hγ
  have hu'Δ := inv_mem_AΔ ((HW l).W K 1 LL hG) huΔ hu.val_inv_mul
  have hpt : ∀ ζ τ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → ζ ^ ((D.loc l).PD K).p = 1 ∧ ζ ≠ 1 := by
    intro ζ τ hPt
    obtain ⟨τs, hIs, -⟩ := hPt
    have hz1 : (D.loc l).ζQ 1 ^ l = 1 := by
      rw [(D.loc l).ζQ_succ 0, (D.loc l).ζQ_zero]
    have hmem : (D.loc l).ζQ 1 ∈ Ks K 1 :=
      le_sup_right (a := K0 K) (IntermediateField.subset_adjoin _ _ (by rw [pow_one]; exact hz1))
    have hy := hIs.2 ⟨_, hmem⟩ rfl
    have hyl : (⟨_, hmem⟩ : ↥(Ks K 1)) ^ l = 1 := Subtype.ext (by simpa using hz1)
    refine ⟨?_, ?_⟩
    · rw [hp, ← hy, ← map_pow, hyl, map_one]
    · intro h1
      rw [← hy] at h1
      have : (⟨_, hmem⟩ : ↥(Ks K 1)) = 1 := τs.toRingHom.injective (by rw [map_one]; exact h1)
      exact (D.loc l).ζQ_one (congrArg Subtype.val this)
  exact modelF_local ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h'
    (MK l K h') (sigA l (sK l K) h') c α β hfr hcry hjmp hs hM hπΔ hEΔ hπu
    (Units.inv_mul w) hQ hu'Δ hu.val_inv_mul (by rw [hgam]; exact hγ) (h5a c)
    (fun y hy => ninLamPf_local ((HW l).W K 1 LL hG) T _ h' w hs hw h5b c hy) (h4W T hcry)
    hpt (hP l hl K LL hG T h' hh' hcry hjmp)

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfH
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLH

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem γLA_smulLA (b : LetA O n) (z : LA W T π' c) :
    γLA W T π' c (smulLA W T π' c b z) = smulLA W T π' c (W.γA W.gamK b) (γLA W T π' c z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e s =>
    show W.γE W.gamK (algebraMap (LetA O n) W.EE b * e) ⊗ₜ s =
      (algebraMap (LetA O n) W.EE (W.γA W.gamK b) * W.γE W.gamK e) ⊗ₜ s
    rw [map_mul, W.γE_ext]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem γA_mem_AΔ {a : LetA O n} (ha : a ∈ W.AΔ) : W.γA W.gamK a ∈ W.AΔ := by
  intro δ hδ
  have e1 : W.γA δ (W.γA W.gamK a) = W.γA (δ * W.gamK) a := by
    simp only [LocWach.γA, map_mul]
    rfl
  have e2 : W.γA W.gamK (W.γA δ a) = W.γA (W.gamK * δ) a := by
    simp only [LocWach.γA, map_mul]
    rfl
  rw [e1, mul_comm, ← e2, ha δ hδ]

theorem rep_γ {u₀ : LetA O n} (hu₀ : u₀ ∈ W.AΔ) (hΛ : u₀ * W.γA W.gamK (Eπ ^ h') = Eπ ^ h')
    (hlet : W.γA W.gamK (letE c : LetA O n) = letE c)
    {x : LA W T π' c} {m : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T}
    (hr : IsRepL W T π' Eπ h' c x a y) :
    IsRepL W T π' Eπ h' c (γLA W T π' c x)
      (fun j => ⟨u₀ * W.γA W.gamK (a j), W.AΔ.mul_mem hu₀ (γA_mem_AΔ W (a j).2)⟩) y := by
  obtain ⟨hy, hx⟩ := hr
  refine ⟨hy, ?_⟩
  have e : smulLA W T π' c (Eπ ^ h') (γLA W T π' c x) =
      smulLA W T π' c u₀ (γLA W T π' c (smulLA W T π' c (Eπ ^ h') x)) := by
    rw [γLA_smulLA, MLE.smulLA_smulLA, hΛ]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, hx, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  show (algebraMap (LetA O n) W.EE u₀ * W.γE W.gamK (algebraMap (LetA O n) W.EE
      ((letE c : LetA O n) * a j))) ⊗ₜ mkL W T π' c (y j) (hy j) = _
  rw [W.γE_ext, ← map_mul]
  congr 2
  show u₀ * W.γA W.gamK ((letE c : LetA O n) * a j) = (letE c : LetA O n) * (u₀ * W.γA W.gamK (a j))
  rw [map_mul, hlet]
  ring

theorem expS_γ (ζ : LL) (u : LL) (hlev : ∀ a, W.lev c ζ (W.γA W.gamK a) = PowerSeries.rescale u (W.lev c ζ a))
    {m : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T) (i : ℤ) :
    expS W T c ζ (fun j => W.γA W.gamK (a j)) y i = u ^ i.toNat • expS W T c ζ a y i := by
  simp only [expS, serC, hlev, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rw [PowerSeries.coeff_rescale, mul_smul]
  · rw [smul_zero]

theorem nl_γ {u₀ : LetA O n} (hu₀ : u₀ ∈ W.AΔ) (hΛ : u₀ * W.γA W.gamK (Eπ ^ h') = Eπ ^ h')
    (hlet : W.γA W.gamK (letE c : LetA O n) = letE c) (u : LL)
    (hlev : ∀ τ ζ, Pt c ζ τ → ∀ a, W.lev c ζ (W.γA W.gamK a) = PowerSeries.rescale u (W.lev c ζ a))
    {x : LA W T π' c} (hx : x ∈ NL W T Pt π' Eπ h' c) : γLA W T π' c x ∈ NL W T Pt π' Eπ h' c := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, a, y, hr, hg⟩ := hx
    refine Submodule.subset_span ⟨m, _, y, rep_γ W T π' Eπ h' c hu₀ hΛ hlet hr, fun τ ζ hpt => ?_⟩
    refine MLB.goodF_mul W T c ζ τ h' u₀ (fun j => W.γA W.gamK (a j)) y (fun i => ?_)
    rw [expS_γ W T c ζ u (hlev τ ζ hpt)]
    exact Submodule.smul_mem _ _ (hg τ ζ hpt i)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [LinearMap.map_smul]; exact Submodule.smul_mem _ _ hx

end Generic

end Formalism.MainNotions.N.Ln34.MLH

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfZetaO
section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem u2ringPf_zetaO {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) {ζ : ↥LL.1}
    (hζ : IsPrimitiveRoot ζ l) : ∃ z : ↥(OL LL), IsPrimitiveRoot z l := by
  have hv : 0 ≤ P.v LL ζ := by
    have h1 : P.v LL (ζ ^ l) = 0 := by rw [hζ.pow_eq_one, AddValuation.map_one]
    rw [AddValuation.map_pow] at h1
    cases hq : P.v LL ζ using WithTop.recTopCoe with
    | top =>
      exfalso
      rw [hq] at h1
      obtain ⟨k, hk⟩ : ∃ k, l = k + 1 := ⟨l - 1, by have := (Fact.out : l.Prime).pos; omega⟩
      rw [hk, succ_nsmul, WithTop.add_top] at h1
      exact WithTop.top_ne_zero h1
    | coe q =>
      rw [hq] at h1
      have h2 : ((l • q : ℚ) : WithTop ℚ) = 0 := by rw [WithTop.coe_nsmul]; exact h1
      have h3 : l • q = 0 := by exact_mod_cast h2
      rw [nsmul_eq_mul, mul_eq_zero] at h3
      rcases h3 with h3 | h3
      · exact absurd (by exact_mod_cast h3 : l = 0) (Fact.out : l.Prime).ne_zero
      · rw [h3]; exact le_refl _
  refine ⟨⟨ζ, (P.v_O LL ζ).1 hv⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥(OL LL) ↥LL.1) hζ Subtype.val_injective

theorem u2ring_pf : SecondRingHypothesis := by
  intro D HW F Cm CA CB CK _ l _ hl K LL hG π' E hR h' hh' c
  have hlp : l.Prime := Fact.out
  have : IsDiscreteValuationRing ↥(OL LL) := GenPf.isDVR (D.loc l) LL
  have : CharZero ↥(OL LL) := Formalism.MainNotions.UnusedSlot80.levg_charZero LL
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hV := Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL
  have hpu := Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL hG) hV
  have hpm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) :=
    (IsLocalRing.mem_maximalIdeal _).2 hpu
  have hp0 : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ≠ 0 := Nat.cast_ne_zero.2 (by rw [hpl]; exact hlp.ne_zero)
  have : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [hpl]; exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  have : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := AdicCompletionMax.isAdicComplete_max hp0 hpm
  have hs : 1 ≤ sK l K := DescentValuation.u3downPf_sK_pos hl K LL hG
  have hd := DvdPf.dvdCondition l hl K LL hG
  have hes : eK K * sK l K = ((D.loc l).PD K).p - 1 := by rw [hpl]; exact Nat.mul_div_cancel' hd
  obtain ⟨ζL, hζL⟩ := Formalism.MainNotions.N.zeta_of_good (D.loc l) hG
  obtain ⟨ζ, hζ⟩ := u2ringPf_zetaO (D.loc l) LL hζL
  have hζ' : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by rw [hpl]; exact hζ
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  obtain ⟨a, r, ha, hrm, hE, hnr⟩ := u2ringPfT_split ((HW l).W K 1 LL hG) hR hs hes hpm c ζ hζ' hp2 hι hRv
  exact u2ringPfD_main ((HW l).W K 1 LL hG) hR hs (((HW l).W K 1 LL hG).gamK_eq_one hs1 hp2) le_rfl c a ha r
    hrm hE hnr h' hh'

end Formalism.MainNotions.N.Ln34
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalLiftRingMembership
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules PowerSeries

set_option maxHeartbeats 1000000 in
open Formalism.MainNotions.N.Ln34.ModelFPf in
theorem universal_lift_ring_membership (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) :
    Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ ∧ π' ∈ ((HW l).W K 1 LL hG).AΔ ∧
    IsUnit (algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) ((HW l).W K 1 LL hG).EE (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) ∧
    IsUnit (algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) ((HW l).W K 1 LL hG).EE π') ∧
    ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam ∧
    (∃ uE ∈ ((HW l).W K 1 LL hG).AΔ, ∃ uE' ∈ ((HW l).W K 1 LL hG).AΔ, uE' * uE = 1 ∧
      ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = uE * Formalism.MainNotions.DeltaInvariantLattices.Eat E π') ∧
    (∃ uπ ∈ ((HW l).W K 1 LL hG).AΔ, ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam π' = π' * uπ) := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  obtain ⟨hπΔ, -, ⟨w0, hw0⟩, -, ⟨w, hw⟩, -, ⟨w2, hw2⟩, -⟩ := hp9
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have hEΔ : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ := by
    intro δ hδ
    funext i
    show ((HW l).W K 1 LL hG).γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply]
    exact congrArg (fun t => Polynomial.aeval t (E i)) (congrFun (hπΔ δ hδ) i)
  have hπu : IsUnit (algebraMap (LetA _ _) ((HW l).W K 1 LL hG).EE π') := by
    rw [hw0, map_mul, map_pow]
    exact (w0.isUnit.map _).mul (((HW l).W K 1 LL hG).EE_π.pow _)
  have hEu : IsUnit (algebraMap (LetA _ _) ((HW l).W K 1 LL hG).EE (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) := by
    have hq := Formalism.MainNotions.LiftingTheory.liftb_q_unit ((HW l).W K 1 LL hG)
    rw [hw, map_mul] at hq
    exact isUnit_of_mul_isUnit_right hq
  obtain ⟨u, hu, hγ⟩ := gam_unit ((HW l).W K 1 LL hG) π' E hsK w2 hw2 w0 hw0
  have hpO : (((D.loc l).PD K).p : ↥(OL LL)) ≠ 0 := fun h0 => by
    apply p_ne_zero ((HW l).W K 1 LL hG)
    rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1), h0, map_zero]
  have hnz := Eπ_nzd ((HW l).W K 1 LL hG) hw (q0_ne_two_and_ne_q_and_ne_d ((HW l).W K 1 LL hG) hpO)
  have huΔ := u_mem_AΔ ((HW l).W K 1 LL hG) hEΔ hnz hγ
  have hu'Δ := inv_mem_AΔ ((HW l).W K 1 LL hG) huΔ hu.val_inv_mul
  have hnzπ : ∀ a : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)), a * π' = 0 → a = 0 := by
    intro a ha
    apply ((HW l).W K 1 LL hG).EE_inj
    have h1 := congrArg (algebraMap (LetA _ _) ((HW l).W K 1 LL hG).EE) ha
    rw [map_mul, map_zero] at h1
    rw [map_zero]
    exact hπu.mul_left_eq_zero.1 h1
  have hγπ : ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam π' =
      (1 + (w2 : LetA _ _) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π') * π' := by
    rw [sub_eq_iff_eq_add] at hw2
    rw [hw2]
    ring
  exact ⟨hEΔ, hπΔ, hEu, hπu, ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl),
    ⟨u, huΔ, _, hu'Δ, hu.val_inv_mul, hγ⟩,
    ⟨_, u_mem_AΔ ((HW l).W K 1 LL hG) hπΔ hnzπ hγπ, by rw [hγπ]; ring⟩⟩

theorem universal_lift_points (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    constantCoeff (((HW l).W K 1 LL hG).lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) = 0 ∧
    coeff 1 (((HW l).W K 1 LL hG).lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) ≠ 0 ∧
    constantCoeff (((HW l).W K 1 LL hG).lev c ζ π') ≠ 0 ∧
    ∀ a, ((HW l).W K 1 LL hG).lev c ζ (((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam a) =
      rescale (algebraMap ↥(OL LL) ↥LL.1 ((Formalism.MainNotions.DeltaInvariantLattices.uU ((HW l).W K 1 LL hG) : (↥(OL LL))ˣ) : ↥(OL LL)))
        (((HW l).W K 1 LL hG).lev c ζ a) := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hζ : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by
    rw [hp]
    exact framepf_pt_prim D HW hG c ζ τ hpt
  obtain ⟨-, -, ⟨w0, hw0⟩, -, ⟨w, hw⟩, -, -, -⟩ := hp9
  obtain ⟨e₁, he₁, he₁0⟩ :=
    DescentValuation.u3downPf_lev_E ((HW l).W K 1 LL hG) c ζ hζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') w hw
  refine ⟨?_, ?_, DescentValuation.u3downPf_cc_π' ((HW l).W K 1 LL hG) c ζ hζ π' (sK l K) w0 hw0, ?_⟩
  · rw [he₁]
    simp
  · rw [he₁, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact he₁0
  · intro a
    have hg := ((HW l).W K 1 LL hG).gam_gen
    exact ((Cm l).C K 1 LL hG).tie.lev_Γ _ c ζ ζ 1 1 (by rw [pow_one]; exact hζ)
      (le_of_eq (by simpa [hs] using hg.symm)) (pow_one ζ).symm a

theorem embeddings_card_le_degree (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    ∃ τs : Finset (↥K.1 →ₐ[ℚ_[l]] ↥LL.1), (∀ τ ζ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → τ ∈ τs) ∧
      τs.card ≤ finrank ↥(K0 K) ↥K.1 := by
  classical
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := by
    apply Nat.finite_of_card_ne_zero
    rw [GenPf.natCard_emb K LL hG]
    exact (Module.finrank_pos (R := ℚ_[l]) (M := ↥K.1)).ne'
  haveI := Fintype.ofFinite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
  haveI : FiniteDimensional ↥(K0 K) ↥K.1 := Module.Finite.right ℚ_[l] ↥(K0 K) ↥K.1
  refine ⟨Finset.univ.filter (fun τ => Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c),
    fun τ ζ hpt => Finset.mem_filter.2 ⟨Finset.mem_univ _, u3upPf_pt_over D HW hG c ζ τ hpt⟩, ?_⟩
  have h := kapPiPf_card ((HW l).W K 1 LL hG) c
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  exact h

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end

