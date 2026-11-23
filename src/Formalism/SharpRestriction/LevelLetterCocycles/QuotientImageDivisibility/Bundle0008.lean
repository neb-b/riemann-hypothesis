module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0006
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.PchainDN
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

section Lin

variable {O : Type} [CommRing O] {A M : Type} [AddCommGroup A] [Module O A] [AddCommGroup M]
  [Module O M]

theorem linLift (K : Submodule O M) (R : A → M → Prop) (hex : ∀ a, ∃ x, R a x)
    (hadd : ∀ a a' x x', R a x → R a' x' → R (a + a') (x + x'))
    (hsmul : ∀ (o : O) a x, R a x → R (o • a) (o • x))
    (huniq : ∀ a x x', R a x → R a x' → x - x' ∈ K) :
    ∃ ψ : A →ₗ[O] M ⧸ K, ∀ a, ∃ x, R a x ∧ ψ a = K.mkQ x := by
  choose g hg using hex
  refine ⟨{ toFun := fun a => K.mkQ (g a), map_add' := ?_, map_smul' := ?_ }, fun a => ⟨g a, hg a, rfl⟩⟩
  · intro a a'
    rw [← map_add (f := _)]
    exact (Submodule.Quotient.eq K).2 (huniq _ _ _ (hg (a + a')) (hadd _ _ _ _ (hg a) (hg a')))
  · intro o a
    rw [RingHom.id_apply, ← map_smul]
    exact (Submodule.Quotient.eq K).2 (huniq _ _ _ (hg (o • a)) (hsmul o _ _ (hg a)))

end Lin

section bigCellDetWeightedEnergyIntegral

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem pchain_DN' (i : ZMod n) (k : ℕ) {m : ℕ} {cc : ℝ} {FF : Type} [AddCommGroup FF]
    [Module O FF] (K : Submodule O ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)) (s : Finset (W.DD T))
    (hs : s.card ≤ m) (hsN : (↑s : Set (W.DD T)) ⊆ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) (L kO : ℕ)
    (hL : Module.length O (↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸
      (Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T))).comap
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype) ≤ (L : ℕ∞))
    (hkO : lenOl PD (O := O) = kO) (hLc : (L : ℝ) ≤ cc * kO) (A : Submodule O FF)
    (ψ : ↥A →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K) :
    Formalism.MainNotions.RamifiedCoefficientChains.S9.PChain (lenOl PD (O := O)) m cc A
      (kerSub A ψ (((Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype).map K.mkQ)) 1 1 := by
  set X := (Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype with hXdef
  set Y := (Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T))).comap
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype with hYdef
  have hXY : X ≤ Y := Submodule.comap_mono le_sup_left
  have hlen : Module.length O ((↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K) ⧸ Y.map K.mkQ) ≤ (L : ℕ∞) := by
    rw [(Submodule.quotientQuotientEquivQuotientSup K Y).length_eq]
    refine le_trans ?_ hL
    exact Module.length_le_of_surjective (Submodule.mapQ Y (K ⊔ Y) LinearMap.id
      (fun y hy => Submodule.mem_sup_right (by simpa using hy)))
      (fun z => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        exact ⟨Submodule.Quotient.mk x, rfl⟩)
  have h1 := pstep_len (m := m) (c := cc) A ψ (Y.map K.mkQ) L kO hlen hkO hLc
  set A₁ := kerSub A ψ (Y.map K.mkQ) with hA₁def
  have hA₁ : A₁ ≤ A := kerSub_le A ψ _
  set ψ₁ : ↥A₁ →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K := ψ.comp (Submodule.inclusion hA₁)
  set sN : Finset ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) := s.subtype (· ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)
  set s' := sN.image K.mkQ
  have hcard : s'.card ≤ m := by
    refine Finset.card_image_le.trans (le_trans ?_ hs)
    rw [Finset.card_subtype]
    exact Finset.card_filter_le _ _
  have hspan : Submodule.span O (↑s : Set (W.DD T)) =
      (Submodule.span O (↑sN : Set ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i))).map
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype := by
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · intro hy
      exact ⟨⟨y, hsN hy⟩, Finset.mem_subtype.2 hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact Finset.mem_subtype.1 hz
  have hY : Y ≤ X ⊔ Submodule.span O (↑sN : Set ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)) := by
    intro z hz
    have hz' : (z : W.DD T) ∈ Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T)) := hz
    obtain ⟨x, hx, t, ht, hxt⟩ := Submodule.mem_sup.1 hz'
    rw [hspan] at ht
    obtain ⟨t', ht', rfl⟩ := Submodule.mem_map.1 ht
    have hxN : x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i := by
      have e : x = (z : W.DD T) - (t' : W.DD T) := by rw [← hxt]; simp
      rw [e]; exact (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).sub_mem z.2 t'.2
    refine Submodule.mem_sup.2 ⟨⟨x, hxN⟩, hx, t', ht', Subtype.ext ?_⟩
    simpa using hxt
  have hgen : ∀ a, ψ₁ a ∈ X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
    intro a
    have ha : ψ ⟨(a : FF), hA₁ a.2⟩ ∈ Y.map K.mkQ := (mem_kerSub_coe A ψ _ ⟨a, hA₁ a.2⟩).1 a.2
    have hle : Y.map K.mkQ ≤ X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
      calc Y.map K.mkQ ≤ (X ⊔ Submodule.span O (↑sN : Set _)).map K.mkQ := Submodule.map_mono hY
        _ = X.map K.mkQ ⊔ (Submodule.span O (↑sN : Set _)).map K.mkQ := Submodule.map_sup _ _ _
        _ = X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
          rw [Submodule.map_span, Finset.coe_image]
    exact hle ha
  have h2 := pstep_gen (lenO := lenOl PD (O := O)) (m := m) (c := cc) A₁ ψ₁ (X.map K.mkQ) s' hcard hgen
  have heq : kerSub A₁ ψ₁ (X.map K.mkQ) = kerSub A ψ (X.map K.mkQ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := (mem_kerSub A₁ ψ₁ _ x).1 hx
      exact (mem_kerSub A ψ _ x).2 ⟨hA₁ hx1, hx2⟩
    · intro hx
      obtain ⟨hx1, hx2⟩ := (mem_kerSub A ψ _ x).1 hx
      have hx1' : x ∈ A₁ := (mem_kerSub A ψ _ x).2 ⟨hx1, Submodule.map_mono hXY hx2⟩
      exact (mem_kerSub A₁ ψ₁ _ x).2 ⟨hx1', hx2⟩
  rw [heq] at h2
  exact (pchain_of_len h1).trans (pchain_of_gen h2)

end bigCellDetWeightedEnergyIntegral

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RhoLiftOf
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem rhoLift_of [NeZero n] (W : LocWach PD LL O v n) (hT2 : Formalism.MainNotions.CrystallineLiftingInputs.TTool2 W)
    (hF : Formalism.MainNotions.CrystallineLiftingInputs.FTool W) (hK : W.ClKNat) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : Formalism.MainNotions.RamifiedCoefficientChains.S9.RhoLift W := by
  intro d T₁ T₂ F b S η m hS c hc w u κ k hu hR hcong
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hp11 : 11 ≤ PD.p := hS.2.1
  have hn : Even n := hS.2.2.1
  obtain ⟨hc1, hc2, -⟩ := hS.2.2.2.2.2.1
  have hcE : (c.val + d) % 2 = 0 := (Finset.mem_filter.1 hc).2
  have hTC : Formalism.MainNotions.CrystallineLiftingInputs.TCase PD.p 1 (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S)) η
      (Formalism.MainNotions.RamifiedCoefficientChains.S9.sigC PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S) η) :=
    Or.inl ⟨rfl, Nat.le_add_left _ _, rfl⟩
  have T2 := hT2 hA hp11 1 _ η _ hTC

  have hwin : ∀ i a, a ∈ Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η i →
      -((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S : ℕ) : ℤ) ≤ a := by
    intro i a ha
    have hbi : b i ≤ Finset.univ.sup b := Finset.le_sup (Finset.mem_univ i)
    have hη := rk_eta_lt W hS i
    unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at ha
    unfold Formalism.MainNotions.RamifiedCoefficientChains.hpar
    split_ifs at ha <;> simp only [Set.mem_union, Set.mem_Icc] at ha <;> push_cast at ha ⊢ <;> omega
  have hwinU : ∀ c' : ZMod n, (c'.val + d) % 2 = 0 → ∀ a,
      a ∈ Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η (c' + 1) → -(η : ℤ) ≤ a := by
    intro c' hc' a ha
    have hpar' := Formalism.MainNotions.RamifiedCoefficientChains.S9.parity_succ hn d c'
    unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at ha
    rw [if_neg (by omega)] at ha
    simp only [Set.mem_union, Set.mem_Icc] at ha
    push_cast at ha
    omega
  have hJ1 : ∀ i τ, Formalism.MainNotions.LiftingTheory.Over W τ i →
      JumpsInV PD T₁.ρ τ (Set.Ici (-((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S : ℕ) : ℤ))) :=
    fun i τ hτ a ha => hwin i a (hS.2.2.2.2.2.2.1 i τ hτ a ha)
  have hJ1U : ∀ (c' : ZMod n) τ, (c'.val + d) % 2 = 0 → Formalism.MainNotions.LiftingTheory.Over W τ (c' + 1) →
      JumpsInV PD T₁.ρ τ (Set.Ici (-(η : ℤ))) :=
    fun c' τ hc' hτ a ha => hwinU c' hc' a (hS.2.2.2.2.2.2.1 (c' + 1) τ hτ a ha)
  have hJ2 : ∀ i τ, Formalism.MainNotions.LiftingTheory.Over W τ i →
      JumpsInV PD T₂.ρ τ (Set.Ici (-((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S : ℕ) : ℤ))) :=
    fun i τ hτ a ha => hwin i a (rk_jumps₂ W hE hC hQ hS i τ hτ a ha)
  have hJ2U : ∀ (c' : ZMod n) τ, (c'.val + d) % 2 = 0 → Formalism.MainNotions.LiftingTheory.Over W τ (c' + 1) →
      JumpsInV PD T₂.ρ τ (Set.Ici (-(η : ℤ))) :=
    fun c' τ hc' hτ a ha => hwinU c' hc' a (rk_jumps₂ W hE hC hQ hS (c' + 1) τ hτ a ha)
  have F1 := hF d T₁ T₂ F b S η m hS T₁ hc1 hJ1 hJ1U
  have F2 := hF d T₁ T₂ F b S η m hS T₂ hc2 hJ2 hJ2U
  dsimp only at F1 F2
  obtain ⟨-, -, F1c3, F1c4, F1c5⟩ := F1
  obtain ⟨-, -, F2c3, F2c4, -⟩ := F2

  have hfin : Module.finrank K₀ K = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId K₀ K) hA.1).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  have hring := (((h9 T₁ hc1) hA.2.1 hA.2.2).2.2 hfin).1
  have hΔπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := hring.1
  have hu0 : ∃ u : (LetA O n)ˣ, W.π₀ = (u : LetA O n) * letπ ^ (PD.p - 1) := hring.2.2.1

  obtain ⟨hwI, hκ, z, x, htr, hx1, hx2, hcl⟩ := hR
  obtain ⟨zu, hzu⟩ := (T2.1 T₁ hc1 c).1 u hu
  obtain ⟨⟨xu, hxu1, hxu2⟩, -⟩ := F1c5 c u zu hcE hu hzu
  have hxuΔ := ((RL.mem_Z1DΔ_iff W T₁ _).1 xu.2).2
  have hxΔ := ((RL.mem_Z1DΔ_iff W T₂ _).1 x.2).2
  have hzuL : (letE (c + 1) : LetA O n) • zu = zu := RL.trunc_letter W T₁ c hu.1.1 hzu
  have hDLu : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₁ (c + 1) (xu : W.DD T₁ × W.DD T₁).1 := by
    refine ⟨by rw [hxu1]; exact hzuL, fun δ hδ => (hxuΔ δ hδ).1⟩
  have hPu : Formalism.MainNotions.CrystallineLiftingInputs.PolesFin W T₁ zu :=
    RL.trunc_polesFin W T₁ c η _ hu hzuL ((T2.1 T₁ hc1 c).2.1 u zu hu hzu).1
      (fun y hy hyl => F1c4 c y hcE hy hyl)
  have hH1f : W.clK T₁ xu ∈ latticeFiniteCohomology PD T₁.L := (F1c3 (c + 1) xu hDLu hxu2).2 (by rw [hxu1]; exact hPu)

  have hIu2 : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ c (W.map F u) := RL.inI_map W F hc1 hc2 hu
  obtain ⟨z2, hz2⟩ := (T2.1 T₂ hc2 c).1 _ hIu2
  obtain ⟨p1, hp1, e1⟩ := T2.2 T₁ T₂ F hc1 hc2 c u zu z2 hu hzu hz2
  have hIw3 : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ c (((PD.p : O) ^ k) • w + (-1 : O) • W.map F u) :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.inI_add W T₂ (Formalism.MainNotions.RamifiedCoefficientChains.S9.inI_smul W T₂ _ hwI)
      (Formalism.MainNotions.RamifiedCoefficientChains.S9.inI_smul W T₂ _ hIu2)
  obtain ⟨z3, hz3⟩ := (T2.1 T₂ hc2 c).1 _ hIw3
  obtain ⟨p2, hp2, e2⟩ := (T2.1 T₂ hc2 c).2.2.2.1 ((PD.p : O) ^ k) (-1) w (W.map F u) z z2 z3
    hwI hIu2 htr hz2 hz3
  have hw3PN : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ k) • w + (-1 : O) • W.map F u) := by
    rw [neg_one_smul, ← sub_eq_add_neg]
    exact hcong
  obtain ⟨p3, hp3, e3⟩ := (T2.1 T₂ hc2 c).2.2.2.2.1 _ z3 hIw3 hw3PN hz3
  have hD1 : ((PD.p : O) ^ k) • z - W.map F zu =
      Formalism.MainNotions.CrystallineLiftingInputs.fMX W (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S)) η • (p3 - p2 - p1) := by
    rw [smul_sub, smul_sub, ← e1, ← e2, ← e3, neg_one_smul]
    abel
  have hP : p3 - p2 - p1 ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T₂ c 1 :=
    Submodule.sub_mem _ (Submodule.sub_mem _ hp3 hp2) hp1
  have hY : Formalism.MainNotions.LiftingTheory.qp W ^ η • (p3 - p2 - p1) ∈ W.N T₂ :=
    F2c4 c _ hcE (RL.pullJ_le_φpull W T₂ c hP) (RL.pullJ_letter W T₂ c hP)
  have hD1Δ : ∀ δ ∈ W.DelF, W.γD T₂ δ (((PD.p : O) ^ k) • z - W.map F zu) =
      ((PD.p : O) ^ k) • z - W.map F zu := by
    intro δ hδ
    rw [map_sub, map_smul, ← W.map_γ, ← hx1, (hxΔ δ hδ).1, ← hxu1, (hxuΔ δ hδ).1]
  have hD1PN : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S))
      (((PD.p : O) ^ k) • z - W.map F zu) :=
    RL.inPN_of_inv W T₂ hu0 hΔπ _ hY (by rw [hD1, Formalism.MainNotions.CrystallineLiftingInputs.fMX, mul_smul]) hD1Δ

  let yu : ↥(W.wachCocyclesDelta T₂) := ⟨_, RL.map_mem_Z1DΔ W F xu⟩
  have hnat : F.H1map (W.clK T₁ xu) = W.clK T₂ yu := hK F xu yu rfl
  have hdd1 : ((((PD.p : O) ^ k) • x - yu : ↥(W.wachCocyclesDelta T₂)) : W.DD T₂ × W.DD T₂).1 =
      ((PD.p : O) ^ k) • z - W.map F zu := by
    simp [yu, hx1, hxu1]
  have hdd2 : ((((PD.p : O) ^ k) • x - yu : ↥(W.wachCocyclesDelta T₂)) : W.DD T₂ × W.DD T₂).2 =
      ((PD.p : O) ^ k) • (x : W.DD T₂ × W.DD T₂).2 + (-1 : O) • W.map F (xu : W.DD T₁ × W.DD T₁).2 := by
    simp [yu, sub_eq_add_neg]
  have hDL2 : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (c + 1)
      ((((PD.p : O) ^ k) • x - yu : ↥(W.wachCocyclesDelta T₂)) : W.DD T₂ × W.DD T₂).1 := by
    rw [hdd1]
    refine ⟨?_, hD1Δ⟩
    rw [smul_sub, smul_comm, RL.trunc_letter W T₂ c hwI.1.1 htr, ← RL.map_smulA, hzuL]
  have hPN2 : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S))
      ((((PD.p : O) ^ k) • x - yu : ↥(W.wachCocyclesDelta T₂)) : W.DD T₂ × W.DD T₂).2 := by
    rw [hdd2]
    exact Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_add W T₂ (Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_smul W T₂ _ hx2)
      (Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_smul W T₂ _ (RL.inPN_map W F hc1 hc2 hxu2))
  have hz0 : W.clK T₂ (((PD.p : O) ^ k) • x - yu) = 0 :=
    (F2c3 (c + 1) _ hDL2 hPN2).1 (by rw [hdd1]; exact hD1PN)
  have hcls : ((PD.p : O) ^ k) • W.clK T₂ x = F.H1map (W.clK T₁ xu) := by
    have e : W.clK T₂ (((PD.p : O) ^ k) • x - yu) =
        ((PD.p : O) ^ k) • W.clK T₂ x - W.clK T₂ yu :=
      ((W.clK T₂).map_sub _ _).trans (congrArg (· - W.clK T₂ yu) ((W.clK T₂).map_smul _ _))
    rw [e] at hz0
    rw [hnat]
    exact sub_eq_zero.1 hz0
  have hmk : (Submodule.Quotient.mk (((PD.p : O) ^ k) • (⟨κ, hκ⟩ : ↥(latticeCocycles T₂.L))) : LatticeCohomology T₂.L) =
      F.H1map (W.clK T₁ xu) := by
    rw [Submodule.Quotient.mk_smul, ← hcl, hcls]
  exact RL.mem_ImF_of_cls F _ ⟨_, hH1f, hmk.symm⟩

theorem rhoLift_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) (hA : Formalism.MainNotions.RamifiedCoefficientChains.admitted D HW F Cm CR CA CB CK)
    (hT : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))],
      Formalism.MainNotions.CrystallineLiftingInputs.TTool2 ((HW l).W K 1 LL hg) ∧ Formalism.MainNotions.CrystallineLiftingInputs.FTool ((HW l).W K 1 LL hg)) :
    Formalism.MainNotions.RamifiedCoefficientChains.S9.rhoLift D HW F := by
  intro l _ K LL hg _
  intro d T₁ T₂ F' b S η m hS
  have h1 := hA.1 l K 1 LL hg
  have h11 := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have h17 := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 l K 1 LL hg
  have hp11 : 11 ≤ ((D.loc l).PD K).p := hS.2.1
  have hK : ((HW l).W K 1 LL hg).ClKNat := h17.2 fun h2 => absurd h2 (by omega)
  exact rhoLift_of _ (hT l K LL hg).1 (hT l K LL hg).2 hK h1.2.2.2.2.2.2.2.2.1 h11.1 h11.2.1
    h11.2.2 d T₁ T₂ F' b S η m hS

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

