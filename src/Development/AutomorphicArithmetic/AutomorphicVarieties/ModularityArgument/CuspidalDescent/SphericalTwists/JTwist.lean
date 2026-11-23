module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.JTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.DualOfWeights
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.GalN.V UpperTheory.V.Z.Win UpperTheory.V.Z.Desc.W UpperTheory.Zero.LLC

private theorem twRep_one {H M : Type} [Group H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M) :
    twRep ρ 1 = ρ := by
  ext g v
  simp [twRep]

private theorem twRep_inv {H M : Type} [Group H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M) (η : H →* ℂˣ) :
    twRep (twRep ρ η⁻¹) η = ρ := by
  ext g v
  simp [twRep, smul_smul]

private theorem locDet_KGL {E : Type} [Field E] [NumberField E] {n : ℕ} {χ : Formalism.L2.Host.HChar E} {w : Plc E}
    (h : χ.UnrAt w) {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) : CuspSub.locDet n χ w g = 1 :=
  h _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hg)

private theorem det_tw {n : ℕ} {k Γ H : Type} [Field k] [Group Γ] [Group H] {D D' : W.GDet n k Γ} {β : Γ →* kˣ}
    {ρ : Γ →* GL (Fin n) k} (φ : H →* Γ) (hD : D = W.GDet.ofRep (W.mat ρ)) (h : D.IsTwist β D') :
    D'.comap φ = W.GDet.ofRep (W.mat (Af.tw (ρ.comp φ) (β.comp φ))) := by
  subst hD
  refine W.GDet.ext fun B _ _ y => (h B _).trans ?_
  change (W.GDet.repAlg _ B _).det = (W.GDet.repAlg _ B y).det
  congr 1
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add (W.GDet.repAlg _ B), ← ha, ← hb, ← map_add (f := _), ← map_add (f := _)]
    congr 2
    exact map_add (MonoidAlgebra.mapDomainRingHom B φ) a b
  | single g r =>
    ext i j
    simp [W.GDet.repAlg, W.mat, Af.tw_val, mul_assoc]

private theorem tw_aut (P : GlobalTheory.Mem.LiteralAutomorphy.LitN) {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} {β : G L Ω →* (Qbar l)ˣ} (hβ : Continuous β)
    {N : ℕ} (hN : β ^ (2 * N + 1) = 1) {c : G (Lp L) Ω} (hc : Af.IsConjEl c)
    (hcβ : ∀ s s' : G L Ω, s'.restrictScalars (Lp L) = c * s.restrictScalars (Lp L) * c⁻¹ → β s' = (β s)⁻¹)
    {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ) :
    ∃ (σ' : Submodule ℂ (UA L n → ℂ)) (art : (AdeleRing (𝓞 L) L)ˣ →* GlobalTheory.HeckeGal.Gab L Ω) (κ : Formalism.L2.Host.HChar L), IsAutRepU σ' ∧ GlobalTheory.HeckeGal.IsGlobalArtin art ∧
      GlobalTheory.HeckeGal.IsLAdicOf art ι κ 0 β ∧
      (∀ φ lam, HasWeightAt σ φ lam → HasWeightAt σ' φ lam) ∧
      (∀ (w : Plc L) (A : ValuationSubring Ω), IsPlaceOver A w → (∀ g ∈ Ine (F := L) A, β g = 1) →
        IsUnramU σ w → IsUnramU σ' w) ∧
      (∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
        ∃ τ' : SmIrr (GLw n w), IsCompAlong σ' (locU n w) ((cLoc w).comp (locU n w).subtype) τ'.ρ ∧
          Nonempty (τ'.ρ.Equiv (twRep τ.ρ (CuspSub.locDet n κ w))) ∧
          ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ g ∈ Ine (F := L) A, β g = 1) →
            ∀ U ≤ GlobalTheory.LFun.KGL w (n := n), fixd τ.ρ U ≠ ⊥ → fixd τ'.ρ U ≠ ⊥) ∧
      ∀ w, IsSplitAt w → ∀ τ' : SmIrr (GLw n w), IsCompAlong σ' (locU n w) ((cLoc w).comp (locU n w).subtype) τ'.ρ →
        ∃ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧
          Nonempty (τ'.ρ.Equiv (twRep τ.ρ (CuspSub.locDet n κ w))) := by
  obtain ⟨art, ha⟩ := P.aut.art L Ω
  have hm : 0 < 2 * N + 1 := Nat.succ_pos _
  have h0 : Continuous (β ^ (N + 1) :) := hβ.pow (N + 1)
  have h1 : (β ^ (N + 1)) ^ (2 * N + 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hN, one_pow]
  have h2 : β ^ (N + 1) * β ^ (N + 1) = β := by
    rw [← pow_add, show N + 1 + (N + 1) = 2 * N + 1 + 1 by ring, pow_succ, hN, one_mul]
  obtain ⟨ν, ⟨hν, hνβ⟩, -⟩ := GlobalTheory.HeckeGal.exists_unique_hchar_of_finite_order ha ι _ h0 hm h1
  have hκ : GlobalTheory.HeckeGal.IsLAdicOf art ι (ν * ν) 0 β := by simpa only [h2, add_zero] using hνβ.mul hνβ
  have hθ := UpperTheory.thetaChar_eq_self_of_conjugate_dual L Ω l ι art ha ν _ hm hν _ h0 hνβ c hc fun s s' e => by
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, hcβ s s' e, inv_pow]
  obtain ⟨g1, g2, g3⟩ := UpperTheory.detCharacter_ker_open_trivial_rational_archimedean L n ν _ hm hν
  have g4 := UpperTheory.detCharacter_eq_localDet_split_nonsplit L n ν hθ
  obtain ⟨σ', a1, a2, a3⟩ := UpperTheory.exists_automorphicRep_twist_by_character L n _ g1 g2 σ hσ
  have a4 : ∀ w, IsSplitAt w → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : Representation ℂ (GLw n w) M),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ ↔
        IsCompAlong σ' (locU n w) ((cLoc w).comp (locU n w).subtype) (twRep τ (CuspSub.locDet n (ν * ν) w)) :=
    fun w hw M _ _ τ => a3 _ _ _ _ τ _ fun x => (g4 w x x.2).1 hw
  refine ⟨σ', art, ν * ν, a1, ha, hκ, fun φ lam h => ?_, fun w A hA hu => a2 w fun g hg hK => ?_,
    fun w hw τ hτ => ⟨τ.twist _ (CuspSub.isOpen_ker_locDet (ν * ν) w), (a4 w hw _ _).1 hτ, ⟨.refl _⟩, fun A hA hu U hU hf => ?_⟩,
    fun w hw τ' hτ' => ?_⟩
  · have := (a3 (embU n φ) _ _ _ _ 1 fun x => g3 x x.2.1).1 h
    rwa [twRep_one] at this
  · by_cases hw : IsSplitAt w
    · exact ((g4 w g hg).1 hw).trans (locDet_KGL ((hκ.unr_iff ha (Or.inr rfl) hA).1 hu) hK)
    · refine ((g4 w g hg).2 hw).trans (locDet_KGL ((hνβ.unr_iff ha (Or.inr rfl) hA).1 fun s hs => ?_) hK)
      rw [MonoidHom.pow_apply, hu s hs, one_pow]
  · obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hf
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun u hu' => ?_, h0⟩
    change ((CuspSub.locDet n (ν * ν) w u : ℂˣ) : ℂ) • τ.ρ u v = v
    rw [locDet_KGL ((hκ.unr_iff ha (Or.inr rfl) hA).1 hu) (hU hu'), hv u hu', Units.val_one, one_smul]
  · let τ := τ'.twist (CuspSub.locDet n (ν * ν) w)⁻¹ (by simpa using CuspSub.isOpen_ker_locDet (a := n) (ν * ν) w)
    have e : twRep τ.ρ (CuspSub.locDet n (ν * ν) w) = τ'.ρ := twRep_inv _ _
    exact ⟨τ, (a4 w hw _ _).2 (e ▸ hτ'), ⟨e ▸ .refl _⟩⟩

section Lev

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω}

private theorem place_under {A : ValuationSubring Ω} {w : Plc L} (h : IsPlaceOver A w) :
    IsPlaceOver A (w.under (𝓞 (Lp L))) := fun x => by
  rw [IsScalarTower.algebraMap_apply (Lp L) L Ω]
  exact h (algebraMap (𝓞 (Lp L)) (𝓞 L) x)

private theorem split_l (v : Vl l L) : IsSplitAt (s.w v.1) :=
  UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v.1) (s.split _ (Or.inl v.2)) _
    (HeightOneSpectrum.ext (Ideal.ext fun x => (place_under (s.hw v.1) x).symm.trans (s.hA v.1 x)))

private theorem split_at_base_place : IsSplitAt (s.w s.v0) :=
  UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (s.split _ (Or.inr (Or.inr rfl))) _
    (HeightOneSpectrum.ext (Ideal.ext fun x => (place_under (s.hw _) x).symm.trans (s.hA _ x)))

private theorem pr_ine (V : s.Lev) {A : ValuationSubring Ω} {w : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ V.S')
    (hA : IsPlaceOver A w) {g : G L Ω} (hg : g ∈ Ine (F := L) A) : V.pr g = 1 := by
  refine Subtype.ext ((QuotientGroup.eq_one_iff (W.resP L Ω g)).2
    (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)))
  simp only [Set.mem_iUnion]
  exact ⟨_, hw, A, place_under hA, hg⟩

private theorem pr_surj (V : s.Lev) : Function.Surjective V.pr := by
  rintro ⟨g, hg⟩
  obtain ⟨g, rfl⟩ : ∃ t, toGS Ω V.S' t = g := QuotientGroup.mk'_surjective _ g
  obtain ⟨t, rfl⟩ := (V.hη g).1 hg
  exact ⟨t, rfl⟩

private theorem pr_conj (V : s.Lev) {g g' : G L Ω}
    (h : g'.restrictScalars (Lp L) = s.c * g.restrictScalars (Lp L) * s.c⁻¹) : V.pr g' = V.frame.conj (V.pr g) := by
  refine Subtype.ext ?_
  change toGS Ω V.S' (g'.restrictScalars (Lp L)) =
    toGS Ω V.S' s.c * toGS Ω V.S' (g.restrictScalars (Lp L)) * (toGS Ω V.S' s.c)⁻¹
  rw [h, map_mul, map_mul, map_inv]

end Lev

private theorem ss_comp {Γ H k : Type} [Group Γ] [Group H] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} {φ : H →* Γ}
    (hφ : Function.Surjective φ) (h : Formalism.MainNotions.N.IsSSRep r) : Formalism.MainNotions.N.IsSSRep (r.comp φ) := fun U hU => by
  obtain ⟨U', h1, h2⟩ := h U fun g v hv => by
    obtain ⟨g, rfl⟩ := hφ g
    exact hU g v hv
  exact ⟨U', fun g v hv => h1 (φ g) v hv, h2⟩

private theorem part_tw {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w} {κ : Dec (F := F) A →* (Qbar l)ˣ} {wt : W.Emb l w → ℤ}
    {ph : Ine (F := F) A →* (Qbar l)ˣ} (H : W.IsWtPart h κ wt ph) {β : G F Ω →* (Qbar l)ˣ} (hβ : IsOpen (β.ker : Set (G F Ω))) :
    W.IsWtPart h (κ * β.comp (Dec (F := F) A).subtype) wt (ph * (β.comp (Ine (F := F) A).subtype)⁻¹) := by
  refine ⟨Subgroup.isOpen_mono (H₁ := ph.ker ⊓ β.ker.comap (Ine (F := F) A).subtype) (fun g hg => ?_)
    (H.1.inter (hβ.preimage continuous_subtype_val)), fun a ha g => ?_⟩
  · have h1 : ph g = 1 := hg.1
    have h2 : β g = 1 := hg.2
    change ph g * (β g)⁻¹ = 1
    rw [h1, h2, inv_one, mul_one]
  · rw [← H.2 a ha g]
    congr 1
    change κ _ * β g * (ph g * (β g)⁻¹) = _
    rw [mul_mul_mul_comm, mul_inv_cancel, mul_one]

private theorem ord_congr {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w} {ι : Qbar l ≃+* ℂ} {a : Weil h →* (w.adicCompletion F)ˣ}
    {ω : (w.adicCompletion F)ˣ →* ℂˣ} {hh : (F →+* Qbar l) → ℤ} {ψ ψ' : Dec (F := F) A →* (Qbar l)ˣ} (H : OrdChar ι a ω hh ψ)
    (e : ∀ g, (ψ g : Qbar l) = ψ' g) : OrdChar ι a ω hh ψ' :=
  (MonoidHom.ext fun g => Units.ext (e g) : ψ = ψ') ▸ H

theorem UpperTheory.V.Z.Desc.W.woGd' {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : Plc E} {h : IsPlaceOver A w} {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {y : WD h}
    (k : WDT ι r y) (g : Gd y) : IsWDOf ι r y := k.isWDOf g

section Pt

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (Q : QData V) {c : Coef l} {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ι : Qbar l ≃+* ℂ)

def UpperTheory.V.Z.Desc.W.PartOf (lam : Wt L l n) (d : ℕ) (ξ : GV n (hset Q τ₀).Sl →* GL (Fin d) ℂ) (Y : (hset Q τ₀).Part ι lam ξ) : Prop :=
  ∃ (σ : Submodule ℂ (UA L n → ℂ)) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)),
    IsAutRepU σ ∧ IsBasis ι e ξ ∧ YOf Q ι τ₀ e ξ σ ≠ ⊥ ∧
    (∀ v : V.frame.Vl, IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) (Y.σl v).ρ) ∧
    ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
      Af.LocGlob ι (Y.r.comp V.pr) w τ

private theorem autP (hP : Af.HypothesesH) (hn : 1 ≤ n) (r : Resid V.frame c.O n) (hτ : TypeFor r ι τ₀) :
    Z.Ord.AutY (hset Q τ₀) ι (PartOf Q τ₀ ι) := by
  intro lam _ d ξ hξ F hF hK hI
  obtain ⟨e, he⟩ := hξ
  have hTeich : ∃ t, r.IsTeich t := by
    obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
    have : CharP (ResidueField c.O) l := by
      refine (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 ?_
      rw [← map_natCast (residue c.O), residue_eq_zero_iff]
      exact hlm
    have : CharP (c.O ⧸ maximalIdeal c.O) l := inferInstanceAs (CharP (ResidueField c.O) l)
    have : PerfectRing (ResidueField c.O) l := inferInstance
    let lift := Perfection.lift l (ResidueField c.O) (c.O ⧸ maximalIdeal c.O)
    let j := lift (RingHom.id (ResidueField c.O))
    let τ := (Perfection.teichmuller l (maximalIdeal c.O)).comp j.toMonoidHom
    have hres (x : ResidueField c.O) : residue c.O (τ x) = x :=
      (Perfection.mk_teichmuller (j x)).trans
        (RingHom.congr_fun (lift.symm_apply_apply (RingHom.id (ResidueField c.O))) x)
    refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hres _, ?_⟩⟩
    rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
  obtain ⟨t, ht⟩ := hTeich
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) := by
    let f := ι.toRingHom.comp (algebraMap c.O (Qbar l))
    have hf : Function.Injective f := ι.injective.comp Subtype.val_injective
    have hmap : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin m) f) := by
      intro A B hAB
      apply Units.ext
      apply Matrix.ext
      intro i j
      exact hf (congrArg (fun M : GL (Fin m) ℂ => (M : Matrix (Fin m) (Fin m) ℂ) i j) hAB)
    rw [← MonoidHom.ker_comp_of_injective τ₀ _ hmap]
    exact (hτ t ht).1
  have h1 := decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI
  refine SetLike.le_def.1 (iSup_le fun σ => ?_) h1
  by_cases h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥
  · rw [h0]; exact bot_le
  · obtain ⟨Y, hY, -, hcomp, hLG⟩ := partU hP l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0
    rw [← hY]
    exact le_iSup (fun Y : {Y : (hset Q τ₀).Part ι lam ξ // PartOf Q τ₀ ι lam d ξ Y} => Y.1.Y) ⟨Y, σ.1, e, σ.2, he, h0, hcomp, hLG⟩

end Pt


set_option maxHeartbeats 1600000 in
private theorem pt_part (PH : Af.HypothesesH) {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} {Q : QData V} {c : Coef l}
    {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r} {Λ : LamObj r} {R : HD Q ι Λ} {K : (hset Q R.τ₀).Lev}
    {J : Ideal B.B} (hJ : R.IsJ B K J) {x : B.Pt} (hx : J ≤ RingHom.ker x) {lam : Wt L l n}
    (hg : (hset Q R.τ₀).Good R.θ (x.comp (Λ.toPair B.u)).toRingHom lam) :
    ∃ (d : ℕ) (ξ : GV n (hset Q R.τ₀).Sl →* GL (Fin d) ℂ) (Y : (hset Q R.τ₀).Part ι lam ξ), PartOf Q R.τ₀ ι lam d ξ Y ∧
      x.D = W.GDet.ofRep (W.mat Y.r) ∧ ∀ v : V.frame.Vl, ∃ ω : Fin n → ((s.w v.1).adicCompletion L)ˣ →* ℂˣ,
        IsSubquotient (Y.σl v).ρ (PS ω) ∧ ∀ i, OrdChar ι (artOf (s.hw v.1)) (ω i) (htW lam i) (x.psi v i) := by
  have P := PH.litN
  rcases hJ with ⟨-, rfl⟩ | ⟨_, _, f, -, hf, hs, hl, rfl⟩
  · exact absurd ((map_one x).symm.trans (hx Submodule.mem_top)) one_ne_zero
  obtain ⟨y, hy⟩ : ∃ y : (hset Q R.τ₀).TK R.θ R.a K →ₐ[c.O] Qbar l, ∀ b, y (f b) = x b :=
    ⟨_, AlgHom.liftOfSurjective_apply f hs x hx⟩
  have e1 : y.toRingHom.comp (algebraMap Λ.Λ _) = (x.comp (Λ.toPair B.u)).toRingHom :=
    RingHom.ext fun b => (congrArg y (hl b).symm).trans (hy _)
  have e2 : y.toRingHom.comp f.toRingHom = (x : B.B →+* Qbar l) := RingHom.ext hy
  rw [← e1] at hg
  obtain ⟨d, ξ, Y, h1, h4, h5⟩ := Z.Ord.coreOrd P L Ω l n c _ (axU P l L Ω s n hn V Q c R.m R.τ₀) Λ.Λ R.θ R.isWt ι _
    (autP Q R.τ₀ ι PH hn r R.type) R.a K _ _ hf lam trivial y hg.2.1
  refine ⟨d, ξ, Y, h1, ((congrArg B.u.D.map e2.symm).trans ((CA.d_gmap B.u.D).2.1 _ _).symm).trans h4, fun v => ?_⟩
  obtain ⟨ω, w1, w2⟩ := h5 v
  refine ⟨ω, w1, fun i => ?_⟩
  exact ord_congr (w2 i) fun g => hy _

