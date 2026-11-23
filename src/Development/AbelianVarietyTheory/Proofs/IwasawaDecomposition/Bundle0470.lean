module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperLeftBlockEqOneIffOfFullRank
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0244
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdelicPointCarriesRowLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem mem_baseLevel_iff_finiteGroup_lift (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {g0 : G0 R.Pg D.R.r} {κ : GA D (Yc D 0)}
    (hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) :
    κ ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P) ↔ g0 ∈ P.H := by
  have e : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = g0 := hl.2.2
  show κ ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) κ ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P) ∧
    rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) ∈ P.H) ↔ _
  rw [e]
  exact ⟨fun hk => hk.2.2, fun hg => ⟨hl.1, hl.2.1, hg⟩⟩

theorem baseLevelCharacter_eq_blockCharacter_lift (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {g0 : G0 R.Pg D.R.r} {κ : GA D (Yc D 0)}
    (hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) (hg : g0 ∈ P.H) :
    levChi (Yc D 0) (R.βY 0) (R.dat0 P) κ = ((P.chi ⟨g0, hg⟩ : ℂˣ) : ℂ) := by
  have e : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = g0 := hl.2.2
  have e2 : levFn (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = ext1 P.H P.chi (rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ)) := by
    show ext1 P.H P.chi _ * (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ = _
    simp
  unfold levChi
  rw [e2, e, extendOne_of_mem _ hg]

end GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levChi_flag_triv (R : RealDat D A Ks) (κ : GA D (Yc D 0)) :
    levChi (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) κ = 1 := by
  unfold levChi
  show ((ext1 (⊤ : Subgroup (G0 R.Pg D.R.r)) (⇑(1 : (⊤ : Subgroup (G0 R.Pg D.R.r)) →* ℂˣ)) _ *
    (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ : ℂˣ) : ℂ) = 1
  unfold ext1
  split_ifs <;> simp

theorem hasType_flag1 (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (F : GA D (Yc D 0) → ℂ)
    (hF : ∀ k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P), ∀ g, F (g * k) = levChi (Yc D 0) (R.βY 0) (R.dat0 P) k * F g) :
    HasType (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) F := by
  intro κ hκ g
  have h1 : κ ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) κ ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) ∧
      rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) κ) ∈ (⊥ : Subgroup (G0 R.Pg D.R.r))) := hκ
  have e : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = 1 := Subgroup.mem_bot.1 h1.2.2
  have hJ : κ ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P) := by
    show κ ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) κ ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P) ∧
      rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) ∈ P.H)
    rw [e]
    exact ⟨h1.1, h1.2.1, P.H.one_mem⟩
  have c1 : levChi (Yc D 0) (R.βY 0) (R.dat0 P) κ = 1 := by
    unfold levChi
    show ((ext1 P.H P.chi (rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ)) *
      (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ : ℂˣ) : ℂ) = 1
    rw [e]
    have h2 : ext1 P.H (⇑P.chi) (1 : G0 R.Pg D.R.r) = 1 := blockDiagonalExtendByOnePrimeField_one P.H P.chi
    erw [h2]
    simp
  have c2 : levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) κ = 1 := by
    unfold levChi
    show ((ext1 (⊥ : Subgroup (G0 R.Pg D.R.r)) (⇑(1 : (⊥ : Subgroup (G0 R.Pg D.R.r)) →* ℂˣ)) _ *
      (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ : ℂˣ) : ℂ) = 1
    unfold ext1
    split_ifs <;> simp
  rw [hF κ hJ g, c1, c2]

theorem mult_act_of_lift (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {g0 : G0 R.Pg D.R.r} {κ : GA D (Yc D 0)}
    (hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) :
    ∀ T ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 P)) (levChi (Yc D 0) (R.βY 0) (R.dat0 P)),
      ∀ (v : (MP R).Vec) (g : GA D (Yc D 0)),
        (T : MMap (MP R)) v (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 ((T : MMap (MP R)) v) g := by
  intro T hT
  induction hT using Submodule.span_induction with
  | mem T hT =>
    intro v g
    have hF := hasType_flag1 R P (T v) (fun k hk g' => hT.lev v k hk g')
    have := level_action_spec hF ⟨κ, hl⟩ κ hl g
    show T v (g * κ) = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (T v) g
    rw [this, levChi_flag_triv, inv_one, one_mul]
  | zero =>
    intro v g
    show (0 : GA D (Yc D 0) → ℂ) (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (0 : GA D (Yc D 0) → ℂ) g
    rw [map_zero]
    rfl
  | add T₁ T₂ _ _ h₁ h₂ =>
    intro v g
    show (T₁ v + T₂ v) (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (T₁ v + T₂ v) g
    rw [map_add (f := _), Pi.add_apply, Pi.add_apply, h₁ v g, h₂ v g]
  | smul a T _ hT =>
    intro v g
    show (a • T v) (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (a • T v) g
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, hT v g]

end GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

theorem isRedHom_conj {D : D7} {X : HidaSetting D} {red : X.B.I.Gf → G0g D.nd}
    {b' : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E} (c : G0g D.nd) (hred : IsRedHom X red)
    (hf : FixRed X (fun k => c⁻¹ * red k * c) b') : IsRedHom X (fun k => c⁻¹ * red k * c) := by
  refine ⟨goodAt_of_fixRed hf, fun k hk k' hk' => ?_, fun γ => ?_, fun k hk => ?_⟩
  · simp only [hred.2.1 k hk k' hk', mul_assoc, mul_inv_cancel_left]
  · obtain ⟨k, hk, e⟩ := hred.2.2.1 (c * γ * c⁻¹)
    exact ⟨k, hk, by simp only [e]; group⟩
  · rw [← hred.2.2.2 k hk]
    show c⁻¹ * red k * c = 1 ↔ red k = 1
    constructor
    · intro e
      calc red k = c * (c⁻¹ * red k * c) * c⁻¹ := by group
        _ = 1 := by rw [e]; group
    · intro e; rw [e]; group

theorem seeAt_exists : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed D → ∃ t, SeeAt R F X h t := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F X h hι hL hlev hpin hE
  obtain ⟨eR, plg, iso, hpl, he, hdiv, heG⟩ := hpin
  obtain ⟨ψ0, hgen, -, π, hπ, hmem, hchi⟩ := hlev
  have hgw : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := by
    intro kv
    have := D.naut.plGw_over kv.1 kv.2
    simp [placesOver] at this
    exact this
  obtain ⟨t₀, ht₀, red, b, hred, hfix, hlift, hcover⟩ := GlobalTheory.Mem.SRe.TrPt.exists_trans D G' Pl0 T A Ks R X h eR plg iso hι hL hpl hdiv heG
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.Mem.SymFrame.conj_symLevel D G' Pl0 T A Ks R X h eR plg iso hι hL hpl hdiv heG ψ0 hgen π hπ red b hred hfix hgw
  obtain ⟨b', hfix'⟩ := _root_.GlobalTheory.Mem.SRe.fixRed_conj D X red b c hgw hfix
  obtain ⟨kc, hkc, hkcv⟩ := hred.2.2.1 c
  have hK : ∀ x, x ∈ X.B.I.Kset ↔ x ∈ GlobalTheory.RowLev.Inhab.Ksub X.B.I := fun x => Iff.rfl
  have hmul := hred.2.1
  have red_one : red 1 = 1 := by
    have e := hmul 1 ((hK 1).2 (Subgroup.one_mem _)) 1 ((hK 1).2 (Subgroup.one_mem _))
    rw [mul_one] at e
    exact left_eq_mul.mp e
  have red_inv : ∀ x ∈ X.B.I.Kset, red x⁻¹ = (red x)⁻¹ := by
    intro x hx
    have hx' : x⁻¹ ∈ X.B.I.Kset := (hK _).2 (Subgroup.inv_mem _ ((hK x).1 hx))
    have e := hmul x⁻¹ hx' x hx
    rw [inv_mul_cancel, red_one] at e
    exact eq_inv_of_mul_eq_one_left e.symm
  have memK : ∀ k ∈ X.B.I.Kset, kc⁻¹ * k * kc ∈ X.B.I.Kset := fun k hk =>
    (hK _).2 (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ((hK _).1 hkc)) ((hK _).1 hk)) ((hK _).1 hkc))
  have red_conj : ∀ k ∈ X.B.I.Kset, red (kc⁻¹ * k * kc) = c⁻¹ * red k * c := by
    intro k hk
    have hkc' : kc⁻¹ ∈ X.B.I.Kset := (hK _).2 (Subgroup.inv_mem _ ((hK _).1 hkc))
    have h1 : kc⁻¹ * k ∈ X.B.I.Kset := (hK _).2 (Subgroup.mul_mem _ ((hK _).1 hkc') ((hK _).1 hk))
    rw [hmul _ h1 _ hkc, hmul _ hkc' _ hk, red_inv _ hkc, hkcv]
  obtain ⟨t, ht⟩ : ∃ t : GA D (D.sp.Y 0), t = (iotaX X h).symm (1, kc) * t₀ := ⟨_, rfl⟩
  have hkap : ∀ k, kap X h t k = kap X h t₀ (kc⁻¹ * k * kc) := by
    intro k
    have e : ((1 : X.B.I.Ginf), kc⁻¹ * k * kc) = ((1, kc) : X.B.I.GA)⁻¹ * (1, k) * (1, kc) := by
      ext <;> simp
    show (t⁻¹ * (iotaX X h).symm (1, k) * t : GA D (D.sp.Y 0)) =
      t₀⁻¹ * (iotaX X h).symm (1, kc⁻¹ * k * kc) * t₀
    rw [e, map_mul, map_mul, map_inv, ht]
    group
  set red' : X.B.I.Gf → G0g D.nd := fun k => c⁻¹ * red k * c with hred'def
  have hred' : IsRedHom X red' := isRedHom_conj c hred hfix'
  have hliftT : ∀ k ∈ X.B.I.Kset, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (eR.symm (red' k))) (kap X h t k) := by
    intro k hk
    rw [hkap, hred'def]
    simp only
    rw [← red_conj k hk]
    exact hlift _ (memK k hk)
  have key : ∀ k ∈ X.B.I.Kset, (kap X h t k ∈ JR R F ↔ k ∈ X.K2) ∧
      ∀ hJ : kap X h t k ∈ JR R F, chiR R F (kap X h t k) = star (X.chi2 k) := by
    intro k hk
    have hl := hliftT k hk
    have hiff := mem_baseLevel_iff_finiteGroup_lift R (R.levR F true) hl
    have hc1 := (hc k hk).1
    refine ⟨?_, fun hJ => ?_⟩
    · rw [show kap X h t k ∈ JR R F ↔ _ from hiff, hmem, hc1]
    · have hg : R.eG (eR.symm (red' k)) ∈ (R.levR F true).H := hiff.1 hJ
      have hg' : reord π (R.eG (eR.symm (red' k))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H := (hmem _).1 hg
      show levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) (kap X h t k) = _
      rw [baseLevelCharacter_eq_blockCharacter_lift R (R.levR F true) hl hg, hchi _ hg hg']
      exact (hc k hk).2 hg'
  have hio : ∀ k, iotaX X h ((iotaX X h).symm (1, k)) = (1, k) := fun k => (iotaX X h).apply_symm_apply _
  have hconjEq : ∀ k, (t⁻¹)⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹ = (iotaX X h).symm (1, k) := by
    intro k
    group
  have hK2K : ∀ k ∈ X.K2, k ∈ X.B.I.Kset := fun k hk => hk.1
  refine ⟨t, ⟨?_, ?_, eR.symm, red', ?_, ⟨hred', ?_⟩, ?_⟩⟩
  · have e : t = t₀ * (t₀⁻¹ * (iotaX X h).symm (1, kc) * t₀) := by rw [ht]; group
    rw [e]
    exact Subgroup.mul_mem _ ht₀ (hlift kc hkc).1
  · intro y
    have hJ' : ∀ k, (t⁻¹)⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹ ∈ iotaX X h ⁻¹' concreteLevelAdelicSubset X ↔ k ∈ X.K2 := by
      intro k
      rw [hconjEq, Set.mem_preimage, hio]
      exact ⟨fun hh => hh.2, fun hh => ⟨rfl, hh⟩⟩
    have hy : y ∈ JR R F ∨ (t⁻¹)⁻¹ * y * t⁻¹ ∈ iotaX X h ⁻¹' concreteLevelAdelicSubset X → ∃ k ∈ X.B.I.Kset, y = kap X h t k := by
      rintro (hy | hy)
      · have hyF : y ∈ levG (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) := ⟨hy.1, hy.2.1, Subgroup.mem_top _⟩
        obtain ⟨k', hk', e⟩ := hcover y hyF
        refine ⟨kc * k' * kc⁻¹, (hK _).2 (Subgroup.mul_mem _ (Subgroup.mul_mem _ ((hK _).1 hkc) ((hK _).1 hk'))
          (Subgroup.inv_mem _ ((hK _).1 hkc))), ?_⟩
        rw [hkap, e]
        congr 1
        group
      · have h2 : (iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).1 = 1 ∧ (iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).2 ∈ X.K2 := hy
        refine ⟨(iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).2, h2.2.1, ?_⟩
        have e : (iotaX X h).symm (1, (iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).2) = (t⁻¹)⁻¹ * y * t⁻¹ := by
          rw [← h2.1]
          exact (iotaX X h).symm_apply_apply _
        show y = (t⁻¹ * (iotaX X h).symm (1, _) * t : GA D (D.sp.Y 0))
        rw [e]
        group
    refine ⟨⟨fun h1 => ?_, fun h1 => ?_⟩, fun h1 => ?_⟩
    · obtain ⟨k, hk, rfl⟩ := hy (Or.inl h1)
      exact (hJ' k).2 ((key k hk).1.1 h1)
    · obtain ⟨k, hk, rfl⟩ := hy (Or.inr h1)
      exact (key k hk).1.2 ((hJ' k).1 h1)
    · obtain ⟨k, hk, rfl⟩ := hy (Or.inl h1)
      rw [(key k hk).2 h1]
      show adelicCharacterOfHidaSetting X (iotaX X h ((t⁻¹)⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹)) = _
      rw [hconjEq, hio]
      rfl
  · intro k hk
    have hkK := hK2K k hk
    have hJ := (key k hkK).1.2 hk
    exact ⟨hJ, (key k hkK).2 hJ⟩
  · intro k hk T hT v g
    exact mult_act_of_lift R (R.levR F true) (hliftT k hk) T hT v g
  · intro γ
    show star (D.ntypes.e0.coeff γ) = D.what₂.embLL ((idemOf A.X).coeff (eR.symm γ))
    rw [he, MulEquiv.apply_symm_apply, hE γ]

end GlobalTheory.Mem.SRe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSideReadingLevelZeroMoved
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.GoodSideLattices

open NumberField IsDedekindDomain

def locMeet {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V] {ι : Type}
    (P : ι → HeightOneSpectrum (𝓞 K)) (S : ι → Submodule (𝓞 K) V) : Submodule (𝓞 K) V where
  carrier := {x | ∀ w, ∃ d : 𝓞 K, d ∉ (P w).asIdeal ∧ d • x ∈ S w}
  zero_mem' := fun w => ⟨1, fun h => (P w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  add_mem' := by
    intro x y hx hy w
    obtain ⟨a, ha, hax⟩ := hx w
    obtain ⟨b, hb, hby⟩ := hy w
    refine ⟨a * b, fun h => ?_, ?_⟩
    · rcases (P w).isPrime.mem_or_mem h with h | h
      exacts [ha h, hb h]
    · rw [smul_add]
      refine (S w).add_mem ?_ ?_
      · rw [mul_comm, mul_smul]
        exact (S w).smul_mem _ hax
      · rw [mul_smul]
        exact (S w).smul_mem _ hby
  smul_mem' := by
    intro c x hx w
    obtain ⟨a, ha, hax⟩ := hx w
    exact ⟨a, ha, by rw [smul_comm]; exact (S w).smul_mem c hax⟩

theorem majAt_cast {K : Type} [Field K] [NumberField K] [StarRing K] {a b : ℕ} (h : a = b)
    (M : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ) (M' : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (v : InfinitePlace K)
    (hM : M' v = (M v).submatrix (Fin.cast h) (Fin.cast h)) (x y : Fin b → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin a)) M' v (x ∘ Fin.cast h) (y ∘ Fin.cast h) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin b)) M v x y := by
  subst h
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord]
  rw [hM]
  rfl

end GlobalTheory.Mem.R3.Rw.GoodSideLattices

namespace GlobalTheory.Mem.R3.Rw.GoodSideLattices


set_option maxHeartbeats 1000000 in
theorem reading_level_zero_of_side_data {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (hP : Pins R F cG) (hH : Holds R F) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (y : Hd R.toRealDat)
    {E1 : Hs} (jE1 : E1.T →ₗ[ℂ] (y.C F.lv2).Amb 0) (n1 : ℕ) (c1 : Module.Basis (Fin n1) ℂ E1.T)
    (Xo1 : InfinitePlace D.what₂.LL → Matrix (Fin n1) (Fin n1) ℂ) (h1 : RrT F y true jE1 n1 c1 Xo1)
    (ε1 : D.div.RR.V ≃ₗ[D.what₂.LL] (Fin n1 → D.what₂.LL))
    (j1 : ∀ x, HEq (Y.Ish.jE (D.jEE x)).1 (jE1 (∑ i, D.what₂.embLL (ε1 x i) • c1 i)))
    (m1 : ∀ v, v ≠ A3.A.v0 → ∀ x x', Formalism.HermitianLatticesTheory.majAt D.div.RR.b D.div.RR.X v x x' =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL (Fin n1)) Xo1 v (ε1 x) (ε1 x'))
    {E0 : Hs} (heq_eigen_embedding_zero : E0.T →ₗ[ℂ] (y.C F.lv2).Amb 0) (n0 : ℕ) (c0 : Module.Basis (Fin n0) ℂ E0.T)
    (Xo0 : InfinitePlace D.what₂.LL → Matrix (Fin n0) (Fin n0) ℂ) (h0 : RrT F y false heq_eigen_embedding_zero n0 c0 Xo0)
    (ε0 : X0.s.RR.V ≃ₗ[D.what₂.LL] (Fin n0 → D.what₂.LL))
    (j0 : ∀ x, HEq (Y.Iz.jE (X0.s.jEE x)).1 (heq_eigen_embedding_zero (∑ i, D.what₂.embLL (ε0 x i) • c0 i)))
    (m0 : ∀ v, v ≠ A3.A.v0 → ∀ x x', Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X v x x' =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL (Fin n0)) Xo0 v (ε0 x) (ε0 x'))
    (rr : (RowSide.sharp D).RRDef) (rr0 : X0.s.RRDef) : Nonempty (RationalReadingWithoutCongruence R F X0 Y) := by
  obtain ⟨jW, hjW⟩ := GlobalTheory.Mem.CoordW.exists_jW D G Pl0 I0 T A3 Ks R F cG hP hH Y.mj
  obtain ⟨rfl, a1, b1⟩ := h1
  obtain ⟨rfl, a0, b0⟩ := h0
  refine ⟨⟨ε1.symm, ε0.symm, fun x => ?_, fun x => ?_, fun v hv x x' => ?_, fun v hv x x' => ?_, rr, rr0, jW, hjW⟩⟩
  · have h := j1 (ε1.symm x)
    rw [ε1.apply_symm_apply] at h
    exact (eq_of_heq h).trans (a1 x)
  · have h := j0 (ε0.symm x)
    rw [ε0.apply_symm_apply] at h
    exact (eq_of_heq h).trans (a0 x)
  · rw [m1 v hv, ε1.apply_symm_apply, ε1.apply_symm_apply]
    exact majAt_cast rfl _ Xo1 v (b1 v).1 x x'
  · rw [m0 v hv, ε0.apply_symm_apply, ε0.apply_symm_apply]
    exact majAt_cast rfl _ Xo0 v (b0 v).1 x x'

theorem exists_hlat {K : Type} [Field K] [NumberField K] [StarRing K] (e : K →+* ℂ) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (c : Module.Basis (Fin n) ℂ W) (Xo : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (hXo : ∀ v, IsUnit (Xo v).det) {ι : Type} (P : ι → HeightOneSpectrum (𝓞 K)) (S : ι → Set W) :
    ∃ (RR : HLat K) (j : RR.V →ₛₗ[e] W) (ε : RR.V ≃ₗ[K] (Fin n → K)), (∀ v, IsUnit (RR.X v).det) ∧
      (LinearIndependent ℂ (fun i => j (RR.b i)) ∧ Submodule.span ℂ (Set.range (fun i => j (RR.b i))) = ⊤) ∧
      (∀ x : RR.V, Formalism.HermitianLatticesTheory.normAt RR.b RR.X (InfinitePlace.mk e) x = ‖j x‖) ∧ (∀ x, j x = ∑ i, e (ε x i) • c i) ∧
      (∀ v, v ≠ InfinitePlace.mk e → ∀ x x', Formalism.HermitianLatticesTheory.majAt RR.b RR.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) Xo v (ε x) (ε x')) ∧
      ∀ x : RR.V, x ∈ RR.L ↔ ∀ u, ∃ d : 𝓞 K, d ∉ (P u).asIdeal ∧ d • x ∈ Submodule.span (𝓞 K) {z | j z ∈ S u} := by
  classical
  obtain ⟨Xf, hXf, hXfn⟩ := GlobalTheory.exists_frames_normAt_eq_norm K e W n c ⊤
  let X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ := fun v => if v = InfinitePlace.mk e then Xf v else Xo v
  refine ⟨{ V := Fin n → K, ι := Fin n, b := Pi.basisFun K (Fin n), X := X,
            L := locMeet P fun u => Submodule.span (𝓞 K) {z | GlobalTheory.Mem.coordForm e c z ∈ S u} },
    GlobalTheory.Mem.coordForm e c, LinearEquiv.refl _ _, fun v => ?_, ?_, fun x => ?_, fun _ => rfl, fun v hv x x' => ?_, fun _ => Iff.rfl⟩
  · show IsUnit (if v = InfinitePlace.mk e then Xf v else Xo v).det
    split_ifs
    exacts [hXf v, hXo v]
  · have : (fun i => GlobalTheory.Mem.coordForm e c (Pi.basisFun K (Fin n) i)) = c := funext (GlobalTheory.Mem.coordForm_basisFun e c)
    show LinearIndependent ℂ (fun i => GlobalTheory.Mem.coordForm e c (Pi.basisFun K (Fin n) i)) ∧
      Submodule.span ℂ (Set.range (fun i => GlobalTheory.Mem.coordForm e c (Pi.basisFun K (Fin n) i))) = ⊤
    rw [this]
    exact ⟨c.linearIndependent, c.span_eq⟩
  · refine Eq.trans ?_ (hXfn x)
    show Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X _ x = _
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, X, if_true]
  · show Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x x' = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) Xo v x x'
    simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, X, if_neg hv]

end GlobalTheory.Mem.R3.Rw.GoodSideLattices

namespace GlobalTheory.Mem.R3.Rw.GoodSideLattices

@[reducible] def reRow {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)
    (cen : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) →ₐ[ℂ] Module.End ℂ (S.Amb μ))
    (tie : ∀ μ, S.eOp μ = (open Classical in
      if h : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) then cen μ ⟨D.ntypes.e0, h⟩ else 0))
    (RR : HLat D.what₂.LL) (fr : ∀ v, IsUnit (RR.X v).det) (j : RR.V →ₛₗ[D.what₂.embLL] EE)
    (bs : LinearIndependent ℂ (fun i => j (RR.b i)) ∧ Submodule.span ℂ (Set.range (fun i => j (RR.b i))) = ⊤)
    (nm : ∀ x : RR.V, Formalism.HermitianLatticesTheory.normAt RR.b RR.X (InfinitePlace.mk D.what₂.embLL) x = ‖j x‖) : RowSide D EE :=
  { S with cen := cen, eOp_tie := tie, RR := RR, RR_frames := fr, jEE := j, jEE_basis := bs, jEE_norm := nm }

theorem RRset_reRow {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)
    (cen tie RR fr j bs nm) (μ : D.what₂.Tup) : (reRow S cen tie RR fr j bs nm).RRset μ = S.RRset μ := by
  have h : ∀ k, (reRow S cen tie RR fr j bs nm).downTo μ k = S.downTo μ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => exact congrArg (fun φ => φ.comp (S.io μ k)) ih
  have hi : (reRow S cen tie RR fr j bs nm).iota μ = S.iota μ :=
    congrArg (fun φ => (S.multZero μ).toLinearEquiv.toLinearMap ∘ₗ φ ∘ₗ (S.multTop μ).symm.toLinearEquiv.toLinearMap) (h D.R.m)
  exact congrArg (fun φ : S.Amb μ →ₗ[ℂ] EE => φ '' ((fun x => (S.V0 μ ⊓ (S.V0 μ ⊓ LinearMap.ker φ)ᗮ).starProjection x) ''
    ((S.Mtilde μ).carrier ∩ (S.V0 μ : Set (S.Amb μ))))) hi

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o : q.Over}

set_option maxHeartbeats 1000000 in
theorem RRset_side (s s' : Side0 o) (μ : (w.D o.Z).what₂.Tup) : s.p0.s.RRset μ = s'.p0.s.RRset μ :=
  RRset_reRow s'.p0.s s.cen s.tie s.RR s.frames s.jEE s.basis s.norm μ


set_option maxHeartbeats 1000000 in
theorem eq_of_stdIso (m : Moved o) (eR : Gc B w.px ≃* G0g (w.D o.Z).nd) (hR : StdIso (w.st o.Z) w.px eR) :
    m.z.R.eG.trans m.z.cG = eR := by
  obtain ⟨plg, iso, h1, h2⟩ := hR
  obtain ⟨plg₀, iso₀, k1, -, -, k2⟩ := m.z.pins.keep.grp
  refine MulEquiv.ext fun g => funext fun kv => ?_
  exact (Bare.read_unique g (m.z.R.eG g) (m.z.idG g) (plg kv) (plg₀ kv) ((h1 kv).trans (k1 kv).symm) (iso kv) (iso₀ kv)
    (h2 g kv) (k2 g kv)).symm


set_option maxHeartbeats 1000000 in
theorem exists_side (hF : o.Fits) (m : Moved o) {n : ℕ} (c : Module.Basis (Fin n) ℂ (q.p.ch false).EE.T)
    (Xo : InfinitePlace B.LL → Matrix (Fin n) (Fin n) ℂ) (hXo : ∀ v, IsUnit (Xo v).det) {ι : Type}
    (P : ι → HeightOneSpectrum (𝓞 B.LL)) (S : ι → Set (q.p.ch false).EE.T) :
    ∃ (s : Side0 o) (ε : s.RR.V ≃ₗ[B.LL] (Fin n → B.LL)), (∀ x, s.jEE x = ∑ i, B.embLL (ε x i) • c i) ∧
      (∀ v, v ≠ InfinitePlace.mk B.embLL → ∀ x x', Formalism.HermitianLatticesTheory.majAt s.RR.b s.RR.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL (Fin n)) Xo v (ε x) (ε x')) ∧
      ∀ x : s.RR.V, x ∈ s.RR.L ↔ ∀ u, ∃ d : 𝓞 B.LL, d ∉ (P u).asIdeal ∧ d • x ∈ Submodule.span (𝓞 B.LL) {z | s.jEE z ∈ S u} := by
  obtain ⟨RR, j, ε, h1, h2, h3, h4⟩ := exists_hlat B.embLL c Xo hXo P S
  let eR₀ : Gc B w.px ≃* G0g (w.D o.Z).nd := m.z.R.eG.trans m.z.cG
  have hc : (w.D o.Z).ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D o.Z).nd)) := hF.grpAt.cen
  refine ⟨⟨fun μ => (q.p.sA false μ).act.comp (Bare.cenPull eR₀), fun μ => ?_, fun eR hR μ a a' ha x => ?_, RR, h1, j, h2, h3⟩, ε, h4⟩
  · rw [dite_eq_left hc]
    exact Bare.e_eq_act (m.t.tA false μ) (m.t.lawsA false μ) (Bare.cenPull eR₀ ⟨_, hc⟩) fun g =>
      (m.z.good.2 g).trans (Bare.coeff_cenPull eR₀ ⟨_, hc⟩ g).symm
  · have he : eR₀ = eR := eq_of_stdIso m eR hR
    subst he
    exact congrArg (fun z => (q.p.sA false μ).act z x) (Bare.cenPull_eq _ ha)

end GlobalTheory.Mem.R3.Rw.GoodSideLattices

namespace GlobalTheory.Mem.R3.Rw.GoodSideLattices

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o : q.Over}

def Good (m : Moved o) (s : Side0 o) : Prop :=
  ∃ (n : ℕ) (c : Module.Basis (Fin n) ℂ (q.p.ch false).EE.T) (Xo : InfinitePlace B.LL → Matrix (Fin n) (Fin n) ℂ)
    (ε : s.RR.V ≃ₗ[B.LL] (Fin n → B.LL)), RrT m.z.F m.y false (m.t.ch false).jE n c Xo ∧
      (∀ x, s.jEE x = ∑ i, B.embLL (ε x i) • c i) ∧
      (∀ v, v ≠ InfinitePlace.mk B.embLL → ∀ x x', Formalism.HermitianLatticesTheory.majAt s.RR.b s.RR.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL (Fin n)) Xo v (ε x) (ε x')) ∧ s.p0.s.RRDef

set_option maxHeartbeats 1000000 in
theorem exists_good (hF : o.Fits) (m : Moved o) : ∃ s : Side0 o, Good m s := by
  obtain ⟨n, c, Xo, h⟩ := rrT_exists (w.st o.Z).toD7 (Gc B w.px) (PlS B w.px) (PlI B w.px) (TupU w.I (usedOf w.I T Wt))
    (famR (w.st o.Z) w.I hX (usedOf w.I T Wt) m.z.Xg m.z.tr) m.z.core.Q.c.F m.z.R m.z.F m.z.cG m.z.pins m.intersectionNumber_baseChange m.y false
    (q.p.ch false).EE (m.t.ch false).jE (m.t.ch false).jE_inj (m.t.ch false).jE_range
  have hXo : ∀ v, IsUnit (Xo v).det := h.elim fun _ h' v => (h'.2 v).2
  obtain ⟨s', -⟩ := exists_side hF m c Xo hXo (fun u => (w.D o.Z).plEq u) fun _ => ∅
  obtain ⟨s, ε, h1, h2, h3⟩ := exists_side hF m c Xo hXo (fun u => (w.D o.Z).plEq u)
    fun u => s'.p0.s.RRset ((w.D o.Z).what₂.muAt u)
  refine ⟨s, n, c, Xo, ε, h, h1, h2, fun x => (h3 x).trans (forall_congr' fun u => ?_)⟩
  rw [RRset_side s s']
  exact Iff.rfl

set_option maxHeartbeats 1000000 in
theorem read_of_good (hF : o.Fits) (m : Moved o) (s : Side0 o) (hs : Good m s) (Y : Read m.z.R.toRealDat m.z.F.lv2 s.p0)
    (hIsh : ∀ x, HEq (Y.Ish.jE x).1 ((m.t.ch true).jE x)) (hIz : ∀ x, HEq (Y.Iz.jE x).1 ((m.t.ch false).jE x)) :
    Nonempty (RationalReadingWithoutCongruence m.z.R m.z.F s.p0 Y) :=
  hs.elim fun n hs => hs.elim fun c hs => hs.elim fun Xo hs => hs.elim fun ε0 hs => hF.div.1.elim fun ε hε =>
    reading_level_zero_of_side_data m.z.R m.z.F m.z.cG m.z.pins m.intersectionNumber_baseChange s.p0 Y m.y (m.t.ch true).jE q.p.nR q.p.cR q.p.Xo m.t.rr ε
      (fun x => (hIsh _).trans (heq_of_eq (congrArg (m.t.ch true).jE (hε.1 x)))) hε.2
      (m.t.ch false).jE n c Xo hs.1 ε0
      (fun x => (hIz _).trans (heq_of_eq (congrArg (m.t.ch false).jE (hs.2.1 x)))) hs.2.2.1
      (hF.div.2 o.S o.N o.G) hs.2.2.2

end GlobalTheory.Mem.R3.Rw.GoodSideLattices

namespace GlobalTheory.Mem.R3.Rw


set_option maxHeartbeats 1000000 in
theorem exists_side_reading_level_zero : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), ∀ (q : RowPk w z₀) (o : q.Over), Inputs (w.D o.Z) → o.Fits → ∀ m : Moved o, ∃ s : Side0 o, ∀ Y : Read m.z.R.toRealDat m.z.F.lv2 s.p0, Y.tupT = m.y.tupT → (∀ x, HEq (Y.Ish.jE x).1 ((m.t.ch true).jE x)) → (∀ x, HEq (Y.Iz.jE x).1 ((m.t.ch false).jE x)) → (∀ i x, HEq (Y.mj.eW i x) (m.t.lf.eW i x)) → Nonempty (RationalReadingWithoutCongruence m.z.R m.z.F s.p0 Y) :=
  fun _ _ _ _ _ _ _ _ _ _ _ hF m =>
    (GoodSideLattices.exists_good hF m).imp fun s hs Y _ h1 h2 _ => GoodSideLattices.read_of_good hF m s hs Y h1 h2

end GlobalTheory.Mem.R3.Rw

end
end

