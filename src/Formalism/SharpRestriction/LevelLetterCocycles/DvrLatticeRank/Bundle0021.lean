module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0019
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfLocC
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0003
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0020
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0016
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.NinLamPf

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfDat
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

def FramepfBack {T : LocLat G Qp LL O} (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π')) (Eπ : LetA O n) (h' M : ℕ) : Prop :=
  ∀ (H H' K₁ K₂ : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (lam : O),
    H' * H = PowerSeries.C lam • (1 : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) +
      (PowerSeries.X : PowerSeries O) ^ M • K₁ →
    H * H' = PowerSeries.C lam • (1 : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) +
      (PowerSeries.X : PowerSeries O) ^ M • K₂ →
    ∃ Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c,
      (∀ y ∈ LamPS W T Eπ h' c, Φ y ∈ LamLA W T π' Eπ h' c ⊤) ∧
      (∀ y ∈ JP W T π' Eπ h' M c, Φ y ∈ JLA W T π' Eπ h' M c) ∧
      (∀ x ∈ LamLA W T π' Eπ h' c ⊤,
        Φ (framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H x) - lam • x ∈ JLA W T π' Eπ h' M c) ∧
      ∀ y ∈ LamPS W T Eπ h' c,
        framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H (Φ y) - lam • y ∈ JP W T π' Eπ h' M c


include Ct in
set_option maxHeartbeats 1000000 in
theorem framepf_data [IsDomain O] (hι : Function.Injective (algebraMap O LL)) (hT : IsCrys PD T.ρ)
    (hs : W.s = 1) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (c : ZMod n)
    (hprim : ∀ τ ζ, Pt c ζ τ → IsPrimitiveRoot ζ PD.p) (h4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    {e s' : ℕ} {π' : LetA O n} {Ep : ZMod n → Polynomial O} (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' Ep)
    (hs' : 1 ≤ s') (h' M σ : ℕ) (hM1 : 1 ≤ M) (hM : 4 * h' ≤ s' * M) (hK : W.gamK = W.gam)
    (Bs : FramepfBas W T) (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hγN : ∀ y ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam y - y = π' • d)
    (Fs : PowerSeries O)
    (hFs : W.γ₀ W.gam (π' (c - 1)) = PowerSeries.subst (π' (c - 1)) (PowerSeries.X * Fs))
    (hF0 : PowerSeries.constantCoeff Fs = ((W.χΓ W.gam : Oˣ) : O) ^ s')
    (hne : ∀ y : ℕ, 1 ≤ y → (((W.χΓ W.gam : Oˣ) : O) ^ s') ^ y ≠ 1) (aσ : O)
    (haσ : ((PD.p : ℕ) : O) ^ σ = aσ * ∏ y ∈ Finset.Ico 1 M, ((((W.χΓ W.gam : Oˣ) : O) ^ s') ^ y - 1))
    (hB : FramepfBack Bs π' c hπ0 hΔπ hR2 γ0 hu (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' M) :
    ∃ (hh : LcQ W T π' c →ₗ[O] W.DD T)
      (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c),
      (∀ x ∈ LamLA W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c ⊤, Ψ x ∈ LamPS W T (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c) ∧
      (∀ y ∈ LamPS W T (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c, Φ y ∈ LamLA W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c ⊤) ∧
      FramepfData W Pt π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' M σ c T hh Ψ Φ := by
  have huE := framepf_E_unit hR hs
  have hEΔ := framepf_E_Δ hR
  obtain ⟨Γ, hΓ, R, hΓR⟩ := framepf_Γ Bs π' (c - 1) hπ0 hΔπ hR2 hu hγN
  obtain ⟨H, H', ⟨K1, hK1⟩, ⟨K2, hK2⟩, -, -, ⟨K5, hK5⟩, ⟨K6, hK6⟩⟩ :=
    framepf_mats _ hne Fs hF0 R M hM1 aσ _ haσ
  rw [← pow_mul, mul_comm σ 2] at hK5 hK6
  obtain ⟨Φ, hΦL, hΦJ, hβα, hαβ⟩ := hB H H' K5 K6 _ hK5 hK6
  have hγ := framepf_hhx_γ Bs π' c hπ0 hΔπ hR2 γ0 hu (PowerSeries.X * Fs) (by simp) hFs Γ hΓ H K2 M
    (by rw [hΓR]; exact hK2)
  have hmod := framepf_hhx_mod Bs π' c hπ0 hΔπ hR2 γ0 hu _ H K1 hK1
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    have h1 := congrArg (algebraMap O LL) h
    rw [map_natCast, map_zero] at h1
    have := W.v_l
    rw [h1, AddValuation.map_zero] at this
    exact absurd this (by simp)
  obtain ⟨w, hw⟩ := hR.2.2.1
  obtain ⟨w', hw'⟩ := hR.2.2.2.2.1
  refine ⟨_, framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H, Φ,
    framepf_Ψα_Lam Bs π' c hπ0 hΔπ hR2 γ0 hu _ huE hEΔ h' H, hΦL, hγ, hmod,
    framepf_Ψα_tmul Bs π' c hπ0 hΔπ hR2 γ0 hu H, framepf_Ψα_J Bs π' c hπ0 hΔπ hR2 γ0 hu _ h' M H,
    hΦJ, hβα, hαβ, fun x hx hj => ?_, fun x hx hgx => ?_, fun τ ζ hpt x y hxy m a z hrep k hk i hi => ?_⟩
  · exact framepf_JLA_sat π' c (framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu) _ h' M hu huE
      (fun o ho => (mul_eq_zero.1 ho).resolve_left hp0) _ x hx hj
  · obtain ⟨f, hfΔ, hf⟩ := framepf_γπ hR
    obtain ⟨Ff, hFf, -⟩ := hR2 f hfΔ
    obtain ⟨t, ht⟩ := gradNPf_expand π' f hπ0 Ff hFf _ (gradNPf_cc_f W s' w π' f hw hf)
    refine invLiftPf_inj W T π' f t _ hf ht hu hΔπ hγN hK M (fun y hy _ r₀ hr₀ d hd hrd => ?_) x hx
      (by rw [hK]; exact hgx)
    exact invLiftPf_nzd W T π' w s' w.isUnit hw _
      (fun o ho => (mul_eq_zero.1 ho).resolve_left (sub_ne_zero.2 (hne y hy))) Bs.r Bs.b
      (fun j => (Bs.mem j).1) Bs.uniq 1 r₀ d hr₀ hd (by rw [pow_one]; exact hrd)
  · refine framepf_locC Ct T hT hs c ζ (hprim τ ζ hpt) (fun x k hk => ?_) ?_ (fun r hr h => ?_)
      π' _ w w' s' h' M σ hs' hw w'.isUnit hw' hM _
      (fun ℓ => ((mem_NcS W T (c - 1) _).1 (framepf_hhx_mem Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ)).1) hγ hmod
      _ (framepf_Ψα_tmul Bs π' c hπ0 hΔπ hR2 γ0 hu H) x y hxy m a z hrep k hk i hi
    · exact ((h4.1 (c - 1) 1 ⟨0, one_pow _⟩
        (by rw [Formalism.MainNotions.LiftingTheory.wmap_X_one W hs]; exact framepf_lev_π_one _)).1 x k).2 hk
    · rw [W.gam_gen]
      rw [hs, Nat.cast_one]
      exact zero_le_one
    · obtain ⟨y, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ r by omega)
      rw [zpow_natCast, ← map_pow, ← map_one (algebraMap O LL)] at h
      apply hne y (by omega)
      rw [← pow_mul, mul_comm, pow_mul, hι h, one_pow]

end Local

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LatticeFinrank
section
noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem lattice_finrank {O LL V : Type*} [CommRing O] [IsDomain O] [Field LL] [Algebra O LL]
    [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (T : Submodule O V) [Module.Free O T] [Module.Finite O T]
    (hspan : Submodule.span LL (T : Set V) = ⊤) : finrank O T = finrank LL V := by
  classical
  set bT := Module.Free.chooseBasis O T
  set v : Module.Free.ChooseBasisIndex O T → V := fun i => (bT i : V)
  have hli : LinearIndependent O v := bT.linearIndependent.map' T.subtype T.ker_subtype
  have hliLL : LinearIndependent LL v := (LinearIndependent.iff_fractionRing O LL).1 hli
  have hsp : Submodule.span LL (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine Submodule.span_le.2 fun x hx => ?_
    have e : x = ∑ i, bT.repr ⟨x, hx⟩ i • v i := by
      conv_lhs => rw [show x = ((⟨x, hx⟩ : T) : V) from rfl, ← bT.sum_repr ⟨x, hx⟩]
      rw [Submodule.coe_sum]
      rfl
    rw [SetLike.mem_coe, e]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [Module.finrank_eq_card_chooseBasisIndex, ← finrank_top LL V, ← hsp, finrank_span_eq_card hliLL]

set_option maxHeartbeats 1000000 in
theorem r_eq (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (r : ℕ)
    (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) : r = finrank ↥LL.1 T.V := by
  classical
  have : IsFractionRing ↥(OL LL) ↥LL.1 := GenPf.isFractionRing LL
  set W := (HW l).W K 1 LL hG
  have hs : W.s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  obtain ⟨-, ⟨-, -, -, ⟨r0, b, hbΔ, hbu, hbe⟩, -⟩, -⟩ :=
    (hA l K 1 LL hG).2.2.2.2.2.2.2.2.1 T hT hs (by rw [hp]; exact hl)
  obtain ⟨-, huniq, ⟨w₁, hw₁⟩, -⟩ := hp9
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  obtain ⟨bL0⟩ := MQ.basis_L W T π' (sK l K) hsK w₁ hw₁ huniq b hbΔ hbu hbe c
  have h1 : r = r0 := by
    have e1 := Module.finrank_eq_card_basis bL
    have e2 := Module.finrank_eq_card_basis bL0
    simp only [Fintype.card_fin] at e1 e2
    omega

  have hli : LinearIndependent (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (fun j => (⟨b j, (hbΔ j).1⟩ : W.N T)) := by
    refine Fintype.linearIndependent_iff.2 fun g hg => ?_
    have h1 : (∑ j, g j • b j) = 0 := by
      have := congrArg Subtype.val hg
      simpa using this
    obtain ⟨a0, _, hu⟩ := hbu 0 (W.N T).zero_mem
    have e1 := hu g h1.symm
    have e2 := hu 0 (by simp)
    intro i
    rw [e1, ← e2]
    rfl
  have hsp : ⊤ ≤ Submodule.span (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
      (Set.range fun j => (⟨b j, (hbΔ j).1⟩ : W.N T)) := by
    rintro ⟨x, hx⟩ _
    obtain ⟨a, ha, _⟩ := hbu x hx
    have : (⟨x, hx⟩ : W.N T) = ∑ j, a j • (⟨b j, (hbΔ j).1⟩ : W.N T) := by
      apply Subtype.ext
      simp [ha]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let bN := Module.Basis.mk hli hsp
  let bD := IsBaseChange.basis bN (W.N_base T hT)
  have : Nontrivial W.EE := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' : algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) W.EE 0 =
        algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) W.EE 1 := by rw [map_zero, map_one]; exact h
    have h0 := congrFun (W.EE_inj h') 0
    exact zero_ne_one h0
  have h2 : r0 = finrank W.EE (W.DD T) := by
    rw [Module.finrank_eq_card_basis bD, Fintype.card_fin]
  have h3 := (W.DD_free T).2
  have : Module.Free ↥(OL LL) ↥T.L.T := T.L.free
  have : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  rw [h1, h2, h3]
  exact lattice_finrank T.L.T T.L.span

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfG
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

theorem pi_isUnit {ι : Type} {R : ι → Type} [∀ i, Monoid (R i)] (f : ∀ i, R i)
    (h : ∀ i, IsUnit (f i)) : IsUnit f :=
  ⟨⟨f, fun i => ((h i).unit⁻¹ : (R i)ˣ), funext fun i => (h i).mul_val_inv,
    funext fun i => (h i).val_inv_mul⟩, rfl⟩

section Gam

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem gam_unit (π' : LetA O n) (E : ZMod n → Polynomial O) {s' : ℕ} (hs' : 1 ≤ s')
    (w2 : (LetA O n)ˣ) (hw2 : W.γA W.gam π' - π' = (w2 : LetA O n) * π' * Formalism.MainNotions.DeltaInvariantLattices.Eat E π')
    (w0 : (LetA O n)ˣ) (hw0 : π' = (w0 : LetA O n) * letπ ^ s') :
    ∃ u : LetA O n, IsUnit u ∧ W.γA W.gam (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = u * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' := by
  have key : ∀ i, ∃ G : PowerSeries O, (W.γA W.gam (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) i =
      Formalism.MainNotions.DeltaInvariantLattices.Eat E π' i + (W.γA W.gam π' - π') i * G := by
    intro i
    have hi : (W.γA W.gam (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) i =
        Polynomial.aeval ((W.γA W.gam π') i) (E i) := by
      show W.γ₀ W.gam (Polynomial.aeval (π' i) (E i)) = _
      rw [← Polynomial.aeval_algHom_apply]
      rfl
    obtain ⟨G, hG⟩ := Polynomial.sub_dvd_eval_sub ((W.γA W.gam π') i) (π' i)
      ((E i).map (algebraMap O (PowerSeries O)))
    refine ⟨G, ?_⟩
    rw [hi, Polynomial.aeval_def, ← Polynomial.eval_map, Pi.sub_apply, ← hG]
    show _ = Polynomial.aeval (π' i) (E i) + _
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    ring
  choose G hG using key
  refine ⟨1 + (w2 : LetA O n) * π' * G, ?_, ?_⟩
  · refine pi_isUnit _ fun i => ?_
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have h0 : PowerSeries.constantCoeff (π' i) = 0 := by
      rw [hw0]
      show PowerSeries.constantCoeff ((w0 : LetA O n) i * PowerSeries.X ^ s') = 0
      rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
    show IsUnit (PowerSeries.constantCoeff (1 + (w2 : LetA O n) i * π' i * G i))
    rw [map_add (f := _), map_one, map_mul, map_mul, h0, mul_zero, zero_mul, add_zero]
    exact isUnit_one
  · funext i
    rw [Pi.mul_apply, hG i, hw2]
    simp only [Pi.add_apply, Pi.mul_apply, Pi.one_apply]
    ring

theorem u_mem_AΔ {Eπ u : LetA O n} (hEΔ : Eπ ∈ W.AΔ) (hnz : ∀ a : LetA O n, a * Eπ = 0 → a = 0)
    (hu : W.γA W.gam Eπ = u * Eπ) : u ∈ W.AΔ := by
  intro δ hδ
  have h1 : W.γA δ (u * Eπ) = u * Eπ := by rw [← hu, γA_comm, hEΔ δ hδ]
  rw [map_mul, hEΔ δ hδ] at h1
  exact sub_eq_zero.1 (hnz _ (by rw [sub_mul, h1, sub_self]))

theorem inv_mem_AΔ {u u' : LetA O n} (hu : u ∈ W.AΔ) (huu : u' * u = 1) : u' ∈ W.AΔ := by
  intro δ hδ
  have h2 : W.γA δ u' * u = 1 := by rw [← hu δ hδ, ← map_mul, huu, map_one]
  calc W.γA δ u' = W.γA δ u' * (u * u') := by rw [mul_comm u u', huu, mul_one]
    _ = (W.γA δ u' * u) * u' := by ring
    _ = u' := by rw [h2, one_mul]

theorem q0_ne_two_and_ne_q_and_ne_d (hp : ((PD.p : ℕ) : O) ≠ 0) : W.q₀ ≠ 0 := by
  intro h
  have h1 := W.q₀_def
  rw [h, mul_zero] at h1
  have h2 := congrArg (PowerSeries.coeff 1) h1
  have e : (1 + PowerSeries.X : PowerSeries O) ^ PD.p =
      (((Polynomial.X + 1) ^ PD.p : Polynomial O) : PowerSeries O) := by
    push_cast
    ring
  rw [map_zero, map_sub, e, Polynomial.coeff_coe, Polynomial.coeff_X_add_one_pow,
    Nat.choose_one_right, PowerSeries.coeff_one, if_neg one_ne_zero, sub_zero] at h2
  exact hp h2.symm

theorem Eπ_nzd [IsDomain O] {Eπ : LetA O n} {w : LetA O n} (hQ : W.q = w * Eπ) (hq0 : W.q₀ ≠ 0) :
    ∀ a : LetA O n, a * Eπ = 0 → a = 0 := by
  intro a ha
  funext i
  have h := congrFun ha i
  have hE : Eπ i ≠ 0 := fun h0 => by
    have := congrFun hQ i
    change W.q₀ = w i * Eπ i at this
    rw [h0, mul_zero] at this
    exact hq0 this
  exact (mul_eq_zero.1 h).resolve_right hE

end Gam

end Formalism.MainNotions.N.Ln34.ModelFPf

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfG
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLG

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

variable {LL V' : Type} [Field LL] [AddCommGroup V'] [Module LL V']

def Bdd (F : ℤ → V') (m₀ : ℤ) : Prop := ∀ i < m₀, F i = 0

theorem serMul_eq_sum (P : PowerSeries LL) {F : ℤ → V'} {m₀ : ℤ} (hF : Bdd F m₀) (i : ℤ) (M : ℕ)
    (hM : (i - m₀).toNat + 1 ≤ M) :
    serMul P F i = ∑ k ∈ Finset.range M, PowerSeries.coeff k P • F (i - k) := by
  unfold serMul
  apply finsum_eq_sum_of_support_subset
  intro k hk
  rw [Function.mem_support] at hk
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra hkM
  apply hk
  rw [hF (i - k) (by omega), smul_zero]

theorem serMul_bdd (P : PowerSeries LL) {F : ℤ → V'} {m₀ : ℤ} (hF : Bdd F m₀) : Bdd (serMul P F) m₀ := by
  intro i hi
  unfold serMul
  apply finsum_eq_zero_of_forall_eq_zero
  intro k
  rw [hF (i - k) (by omega), smul_zero]

theorem serMul_serMul (P Q : PowerSeries LL) {F : ℤ → V'} {m₀ : ℤ} (hF : Bdd F m₀) (i : ℤ) :
    serMul P (serMul Q F) i = serMul (P * Q) F i := by
  set N := (i - m₀).toNat + 1 with hN
  rw [serMul_eq_sum P (serMul_bdd Q hF) i N le_rfl, serMul_eq_sum (P * Q) hF i N le_rfl]
  have hL : ∀ k ∈ Finset.range N, PowerSeries.coeff k P • serMul Q F (i - k) =
      ∑ j ∈ Finset.range (N - k), (PowerSeries.coeff k P * PowerSeries.coeff j Q) • F (i - (k + j : ℕ)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [serMul_eq_sum Q hF (i - k) (N - k) (by omega), Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_smul]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl hL]
  have hR : ∀ s ∈ Finset.range N, PowerSeries.coeff s (P * Q) • F (i - s) =
      ∑ k ∈ Finset.Ico 0 (s + 1), (PowerSeries.coeff k P * PowerSeries.coeff (s - k) Q) • F (i - s) := by
    intro s _
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_smul,
      Finset.range_eq_Ico]
  rw [Finset.sum_congr rfl hR, Finset.range_eq_Ico, ← Finset.sum_Ico_Ico_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_Ico] at hk
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Nat.add_sub_cancel_left]

theorem serMul_X_pow (h : ℕ) (F : ℤ → V') (i : ℤ) :
    serMul (PowerSeries.X ^ h : PowerSeries LL) F i = F (i - h) := by
  unfold serMul
  rw [finsum_eq_single _ h (fun k hk => by rw [PowerSeries.coeff_X_pow, if_neg hk, zero_smul])]
  rw [PowerSeries.coeff_X_pow, if_pos rfl, one_smul]

theorem serMul_rescale (u : LL) (hu : u ≠ 0) (P : PowerSeries LL) (F : ℤ → V') (i : ℤ) :
    u ^ i • serMul P F i = serMul (PowerSeries.rescale u P) (fun j => u ^ j • F j) i := by
  unfold serMul
  rw [smul_finsum]
  refine finsum_congr (fun k => ?_)
  rw [PowerSeries.coeff_rescale, smul_smul, smul_smul]
  congr 1
  rw [show u ^ i = u ^ (k : ℤ) * u ^ (i - k) by rw [← zpow_add₀ hu]; ring_nf, zpow_natCast]
  ring

end Formalism.MainNotions.N.Ln34.MLG

end
end

