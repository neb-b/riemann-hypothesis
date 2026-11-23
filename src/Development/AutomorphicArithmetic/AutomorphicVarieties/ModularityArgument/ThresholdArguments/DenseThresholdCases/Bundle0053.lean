module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WtBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0042
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ArithmeticPointDecomposition

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWtBridge
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem uc_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (e : ℕ) :
    Uc k e = GroundTheory.LocalField.unitFiltrationUnits k e := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, Ideal.Quotient.eq.1 (congrArg Units.val hu), rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, Units.ext (Ideal.Quotient.eq.2 hu), rfl⟩
section Loc
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion F)ˣ}
private theorem artin_unique (H : GlobalTheory.Published.GlobalArtinReciprocity) {a' : Weil h →* (w.adicCompletion F)ˣ}
    (ha : IsLocalArtin h a) (ha' : IsLocalArtin h a') : a' = a := by
  obtain ⟨art, hart⟩ := H F Ω
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' F Ω art hart w
  exact MonoidHom.ext fun σ => hinj ((ha'.glob art hart _).trans (ha.glob art hart _).symm)
private theorem art_unit (ha : IsLocalArtin h a) (σ : Ine (F := F) A) : a (ineIncl h σ) ∈ Uo (w.adicCompletion F) := by
  have h2 := ha.ord_eq (ineIncl h σ)
  rw [deg_ineIncl, neg_zero] at h2
  exact GlobalTheory.SmGL.ord_eq_zero_iff.1 h2
private theorem art_onto (ha : IsLocalArtin h a) (y : Uo (w.adicCompletion F)) :
    ∃ σ : Ine (F := F) A, a (ineIncl h σ) = y := by
  obtain ⟨s, hs⟩ := ha.surj y
  have hd : deg s = 0 := by
    have h2 := ha.ord_eq s
    rw [hs, GlobalTheory.SmGL.ord_eq_zero_iff.2 y.2] at h2
    omega
  exact ⟨⟨s, actsAs_zero_iff.1 (actsAs_of_deg (a := 0) (b := 0) (by simpa using hd))⟩, hs⟩
private theorem pw_ne (wt : W.Emb l w → ℤ) (x : (w.adicCompletion F)ˣ) :
    ∏ᶠ τ : W.Emb l w, τ.1 (x : w.adicCompletion F) ^ wt τ ≠ 0 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (W.Emb l w)
  rw [finprod_eq_prod_of_fintype]
  exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ((map_ne_zero j.1).2 x.ne_zero)
private noncomputable def pwHom (wt : W.Emb l w → ℤ) : (w.adicCompletion F)ˣ →* (Qbar l)ˣ :=
  MonoidHom.mk' (fun x => Units.mk0 _ (pw_ne wt x)) fun x y => Units.ext (by
    haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
    simp only [Units.val_mul, Units.val_mk0]
    rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
    exact finprod_congr fun j => by rw [map_mul, mul_zpow])
variable {κ : Dec (F := F) A →* (Qbar l)ˣ} {wt : W.Emb l w → ℤ} {f : Uo (w.adicCompletion F) → Qbar l}
private def IsFin (a : Weil h →* (w.adicCompletion F)ˣ) (κ : Dec (F := F) A →* (Qbar l)ˣ) (wt : W.Emb l w → ℤ)
    (f : Uo (w.adicCompletion F) → Qbar l) : Prop :=
  ∀ (σ : Ine (F := F) A) (y : Uo (w.adicCompletion F)), a (ineIncl h σ) = y →
    (κ (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ)) : Qbar l) * f y =
      ∏ᶠ τ : W.Emb l w, τ.1 ((y : (w.adicCompletion F)ˣ) : w.adicCompletion F) ^ (-wt τ)
private theorem part_val (ha : IsLocalArtin h a) (hf : IsFin a κ wt f) {ph : Ine (F := F) A →* (Qbar l)ˣ}
    (hp : W.IsWtPart h κ wt ph) (σ : Ine (F := F) A) (y : Uo (w.adicCompletion F)) (e : a (ineIncl h σ) = y) :
    (ph σ : Qbar l) = f y := by
  have h1 := hp.2 a ha σ
  rw [e, ← hf σ y e, Units.val_mul] at h1
  exact mul_left_cancel₀ (Units.ne_zero _) h1
private theorem locAlg_iff (H : GlobalTheory.Published.GlobalArtinReciprocity) (ha : IsLocalArtin h a) (hf : IsFin a κ wt f) :
    W.IsLocAlg h κ wt ↔ ∃ e, ∀ y : Uo (w.adicCompletion F), (y : (w.adicCompletion F)ˣ) ∈ Uc _ e → f y = 1 := by
  constructor
  · rintro ⟨ph, hp⟩
    haveI := compactSpace_Ine (E := F) A
    have hC : IsClosed ((fun σ : Ine (F := F) A => a (ineIncl h σ)) '' (ph.ker : Set (Ine (F := F) A))ᶜ) :=
      (hp.1.isClosed_compl.isCompact.image ha.cont).isClosed
    have h1 : (1 : (w.adicCompletion F)ˣ) ∉ (fun σ : Ine (F := F) A => a (ineIncl h σ)) '' (ph.ker : Set (Ine (F := F) A))ᶜ := by
      rintro ⟨σ, hσ, e⟩
      refine hσ (Units.ext ?_)
      rw [part_val ha hf hp σ 1 e, ← part_val ha hf hp 1 1 (by simp), map_one]
    obtain ⟨e, -, he⟩ := GroundTheory.LocalField.hasBasis_nhds_one_unitFiltrationUnits.mem_iff.1 (hC.isOpen_compl.mem_nhds h1)
    refine ⟨e, fun y hy => ?_⟩
    obtain ⟨σ, hσ⟩ := art_onto ha y
    rw [uc_eq] at hy
    have h2 : ph σ = 1 := by
      by_contra h3
      exact he hy ⟨σ, h3, hσ⟩
    rw [← part_val ha hf hp σ y hσ, h2, Units.val_one]
  · rintro ⟨e, he⟩
    let ph : Ine (F := F) A →* (Qbar l)ˣ :=
      ((κ.comp (Subgroup.inclusion (Weil_le_Dec h)))⁻¹ * (pwHom fun τ => -wt τ).comp a).comp (ineIncl h)
    have hv : ∀ σ, ((κ (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ)) * ph σ : (Qbar l)ˣ) : Qbar l) =
        ∏ᶠ τ : W.Emb l w, τ.1 (a (ineIncl h σ) : w.adicCompletion F) ^ (-wt τ) := fun σ =>
      congrArg Units.val (mul_inv_cancel_left _ (pwHom (fun τ => -wt τ) (a (ineIncl h σ))))
    refine ⟨ph, Subgroup.isOpen_mono (H₁ := (Uc _ e).comap (a.comp (ineIncl h))) (fun σ hσ => ?_) ?_, fun a' ha' σ => ?_⟩
    · have h1 := hf σ ⟨_, art_unit ha σ⟩ rfl
      rw [he ⟨_, art_unit ha σ⟩ hσ, mul_one, ← hv, Units.val_inj, left_eq_mul] at h1
      exact h1
    · rw [uc_eq]
      exact (GroundTheory.LocalField.isOpen_unitFiltrationUnits e).preimage ha.cont
    · rw [artin_unique H ha ha', hv]
private theorem emb_lt (j : W.Emb l w) (x : 𝓞 F) (hx : x ∈ w.asIdeal) : ‖j.1 (algebraMap F _ (x : F))‖ < 1 := by
  have h1 : Valued.v (algebraMap F (w.adicCompletion F) (x : F)) < 1 := by
    rw [show algebraMap F (w.adicCompletion F) (x : F) = ((x : F) : w.adicCompletion F) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (w.valuation_lt_one_iff_mem x).2 hx
  have h2 := (j.2.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one h1)
  rw [map_zero] at h2
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 (h2.congr fun m => map_pow _ _ _)
private theorem emb_place {w' : Plc F} (j : W.Emb l w) (j' : W.Emb l w')
    (e : j.1.comp (algebraMap F _) = j'.1.comp (algebraMap F _)) : w = w' := by
  by_contra hne
  have h1 : w.asIdeal ⊔ w'.asIdeal = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne w.isMaximal w'.isMaximal fun h => hne (HeightOneSpectrum.ext h)
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (h1 ▸ Submodule.mem_top : (1 : 𝓞 F) ∈ w.asIdeal ⊔ w'.asIdeal)
  have h2 := emb_lt j x hx
  have h3 := emb_lt j' y hy
  rw [← show j.1 (algebraMap F _ (y : F)) = j'.1 (algebraMap F _ (y : F)) from DFunLike.congr_fun e _] at h3
  have h4 := (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h2 h3)
  rw [← map_add (f := _), ← map_add (f := _), show (x : F) + (y : F) = ((x + y : 𝓞 F) : F) from (map_add (algebraMap (𝓞 F) F) x y).symm,
    hxy] at h4
  simp at h4
private theorem emb_inj (j j' : W.Emb l w) (e : j.1.comp (algebraMap F _) = j'.1.comp (algebraMap F _)) : j = j' := by
  refine Subtype.ext (DFunLike.coe_injective ?_)
  refine (HeightOneSpectrum.denseRange_algebraMap (K := F) (v := w)).equalizer j.2 j'.2 ?_
  funext x
  exact DFunLike.congr_fun e x
end Loc
section Glob
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  (s : HidaSetting l L Ω)
private theorem mem_w (v : Plc (Lp L)) (x : 𝓞 (Lp L)) :
    x ∈ v.asIdeal ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) x ∈ (s.w v).asIdeal :=
  (s.hA v x).symm.trans (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x))
private theorem w_inj : Function.Injective s.w := fun v v' e =>
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_w s, mem_w s, e])
private theorem w_over (v : Vl l L) : ((l : ℕ) : 𝓞 L) ∈ (s.w v.1).asIdeal := by
  simpa using (mem_w s v.1 _).1 v.2
private theorem wt_ex {n : ℕ} (h : s.Wt n) (hh : h.Incr) : ∃ lam, WtOf h lam := by
  classical
  let μ : ∀ v : Vl l L, W.Emb l (s.w v.1) → DomWeight n := fun v τ =>
    ⟨fun i => h v i.rev τ - (i.rev : ℕ), fun i j hij => by
      have key : ∀ (d : ℕ) (a b : Fin n), (b : ℕ) = a + d → h v a τ + d ≤ h v b τ := fun d => by
        induction d with
        | zero => intro a b e; rw [show b = a from Fin.ext e]; simp
        | succ d ih =>
          intro a b e
          have h1 := ih a ⟨a + d, by omega⟩ rfl
          have h2 := hh v τ (show (⟨a + d, by omega⟩ : Fin n) < b from by rw [Fin.lt_def]; simp only; omega)
          simp only at h2
          push_cast
          omega
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show ((j.rev : Fin n) : ℕ) ≤ i.rev from Fin.rev_le_rev.2 hij)
      have := key d _ _ hd
      simp only
      omega⟩
  refine ⟨fun σ => if H : ∃ p : Σ v : Vl l L, W.Emb l (s.w v.1), p.2.1.comp (algebraMap L _) = σ then
    μ H.choose.1 H.choose.2 else ⟨0, fun _ _ _ => le_rfl⟩, fun v j τ => ?_⟩
  have H : ∃ p : Σ v : Vl l L, W.Emb l (s.w v.1), p.2.1.comp (algebraMap L _) = τ.1.comp (algebraMap L _) := ⟨⟨v, τ⟩, rfl⟩
  have e : H.choose = ⟨v, τ⟩ := by
    have h1 := H.choose_spec
    generalize H.choose = p at h1
    obtain ⟨v', τ'⟩ := p
    obtain rfl : v' = v := Subtype.ext (w_inj s (emb_place τ' τ h1))
    rw [emb_inj τ' τ h1]
  simp only [htW, lowW, dif_pos H]
  rw [e]
  simp [μ]
end Glob
theorem UpperTheory.V.Hi.arith_good_iff_hset_of_theta_incr_weight :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (θ : (hset Q τ₀).X.I.T →* Λ.Λˣ), IsTheta Q τ₀ Λ θ → ∀ h : s.Wt n, h.Incr → (∃ lam, WtOf h lam) ∧ ∀ lam, WtOf h lam → ∀ x : B.Pt, (x.Arith h ↔ (hset Q τ₀).Arith θ (x.comp (Λ.toPair B.u)).toRingHom lam) ∧ (x.Good h ↔ (hset Q τ₀).Good θ (x.comp (Λ.toPair B.u)).toRingHom lam) := by
  intro N l _ L Ω _ _ _ _ _ _ s n _ V Q c m τ₀ r B Λ θ hθ h hh
  refine ⟨wt_ex s h hh, fun lam hl x => ?_⟩
  have H := N.aut.art
  have ha : ∀ v : Vl l L, IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := fun v =>
    Classical.epsilon_spec (_root_.UpperTheory.V.Z.Win.T2.laArtinLit' N (s.hw v.1))
  have hf : ∀ (v : Vl l L) (i : Fin n), IsFin (artOf (s.hw v.1)) (x.psi v i) (h v i)
      ((hset Q τ₀).finPart θ (x.comp (Λ.toPair B.u)).toRingHom lam v i) := by
    intro v i σ y e
    let g : Dec (F := L) (s.A v.1) := Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) (ineIncl (s.hw v.1) σ)
    have hg : g ∈ V.frame.Iv v := σ.2
    have h1 := congrArg (fun u : Λ.Λˣ => (x.comp (Λ.toPair B.u)) (u : Λ.Λ)) (hθ v i (ineIncl (s.hw v.1) σ) g hg y rfl e)
    have h2 : (x.comp (Λ.toPair B.u)) (Λ.κ v i ⟨g, hg⟩ : Λ.Λ) = x.psi v i g := by
      have h6 := DFunLike.congr_fun (W.LamObj.toPair_spec r Λ B.u v i) (⟨g, hg⟩ : V.frame.Iv v)
      exact congrArg (fun u : B.Bˣ => x (u : B.B)) h6
    have h3 : (x.comp (Λ.toPair B.u)) ((hset Q τ₀).epsV Λ.Λ v g : Λ.Λ) =
        ∏ᶠ τ : W.Emb l (s.w v.1), τ.1 ((y : ((s.w v.1).adicCompletion L)ˣ) : (s.w v.1).adicCompletion L) ^ (1 : ℤ) := by
      have h4 := (UpperTheory.V.Loc.laCyc H (s.hw v.1) (w_over s v)).2 _ (ha v) σ
      rw [e] at h4
      simp only [MonoidHom.one_apply, mul_one, neg_neg] at h4
      rw [← h4]
      refine ((x.comp (Λ.toPair B.u)).commutes (algebraMap ℤ_[l] c.O (cycZ L Ω l g : ℤ_[l]))).trans ?_
      exact (IsScalarTower.algebraMap_apply ℤ_[l] c.O (Qbar l) _).symm
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, Units.val_one, map_one] at h1
    rw [h2, h3] at h1
    haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) (s.w v.1)
    haveI := Fintype.ofFinite (W.Emb l (s.w v.1))
    have h0 : ∀ τ : W.Emb l (s.w v.1), τ.1 ((y : ((s.w v.1).adicCompletion L)ˣ) : (s.w v.1).adicCompletion L) ≠ 0 :=
      fun τ => (_root_.map_ne_zero _).2 (Units.ne_zero _)
    have h5 : ∏ᶠ τ : W.Emb l (s.w v.1), τ.1 ((y : ((s.w v.1).adicCompletion L)ˣ) : (s.w v.1).adicCompletion L) ^ (-h v i τ) =
        ((∏ᶠ τ : W.Emb l (s.w v.1), τ.1 ((y : ((s.w v.1).adicCompletion L)ˣ) : (s.w v.1).adicCompletion L) ^ (1 : ℤ)) ^ (i : ℕ))⁻¹ /
          algPow (s.w v.1) (lowW lam i) ((y : ((s.w v.1).adicCompletion L)ˣ) : (s.w v.1).adicCompletion L) := by
      unfold algPow
      simp only [finprod_eq_prod_of_fintype]
      rw [← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [← hl v i τ, htW, zpow_one, ← zpow_natCast, ← zpow_neg, ← zpow_sub₀ (h0 τ)]
      congr 1
      ring
    rw [mul_right_comm] at h1
    rw [h5, ← eq_inv_of_mul_eq_one_left h1, mul_div_assoc]
    rfl
  have hA : (∀ (v : Vl l L) (j : Fin n), W.IsLocAlg (s.hw v.1) (x.psi v j) (h v j)) ↔
      (hset Q τ₀).Arith θ (x.comp (Λ.toPair B.u)).toRingHom lam := by
    simp only [fun v j => locAlg_iff H (ha v) (hf v j)]
    refine ⟨fun h1 => ?_, fun ⟨e, he⟩ v j => ⟨e, he v j⟩⟩
    choose e he using h1
    haveI : Finite (Vl l L) := inferInstanceAs (Finite V.frame.Vl)
    obtain ⟨E, hE⟩ := (Set.finite_range fun p : Vl l L × Fin n => e p.1 p.2).bddAbove
    refine ⟨E, fun v i y hy => he v i y ?_⟩
    rw [uc_eq] at hy ⊢
    exact GroundTheory.LocalField.unitFiltrationUnits_antitone (hE ⟨(v, i), rfl⟩) hy
  refine ⟨(and_iff_right hh).trans hA, (and_iff_right hh).trans ⟨fun h1 => ?_, fun ⟨_, h1, h2⟩ v => ?_⟩⟩
  · refine ⟨trivial, hA.1 fun v j => ?_, fun v i j hij => ?_⟩
    · obtain ⟨ph, hp, -⟩ := h1 v
      exact ⟨_, hp j⟩
    · obtain ⟨ph, hp, hi⟩ := h1 v
      by_contra hne
      push Not at hne
      refine hij (hi (MonoidHom.ext fun σ => Units.ext ?_))
      rw [part_val (ha v) (hf v i) (hp i) σ ⟨_, art_unit (ha v) σ⟩ rfl,
        part_val (ha v) (hf v j) (hp j) σ ⟨_, art_unit (ha v) σ⟩ rfl]
      exact hne _
  · choose ph hp using hA.2 h1 v
    refine ⟨ph, hp, fun i j hij => ?_⟩
    by_contra hne
    obtain ⟨y, hy⟩ := h2 v i j hne
    obtain ⟨σ, hσ⟩ := art_onto (ha v) y
    exact hy (by rw [← part_val (ha v) (hf v i) (hp i) σ y hσ, ← part_val (ha v) (hf v j) (hp j) σ y hσ, hij])
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThDefs
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open UpperTheory.V.HV GlobalTheory.GalOfCusp
namespace UpperTheory.V.Th
variable {l : ℕ} [Fact l.Prime]
section Pt
variable {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
variable {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) (y : Pt G0.frame O n) (m : ℕ)
variable (T : TWGrp G0)
end Pt
section Mod
variable {L : Loc} {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid G0.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} {J : Ideal B} {D : ℕ}
  (b : TWBase u J Empty D) (x : B →ₐ[O] O)
variable {b} {G : Glob l L} {h : G.Hom G0} {q N : ℕ} (A : OpMod b h q N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (E : ℕ)
end Mod
section Bar
variable (F : GFrame l) {n : ℕ} (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Algebra O (Qbar l)]
  (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l))
end Bar
section Ar
variable {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev}
def LevelAtOrdinaryDeterminantRing {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid V0.frame O n} {B : UniversalOrdinaryDeterminantRing r}
    {J : Ideal B.B} {D : ℕ} (b : TWBase (pairOf B.u) J Empty D) : Prop :=
  ∀ (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (v : Fin q → Plc (Lp L)) (w : Fin q → Plc L)
    (Bq : Fin q → ValuationSubring Ω), (∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) → Function.Injective v → (∀ j, v j ∉ s.S) →
    V.S' = s.S ∪ Set.range v → (∀ j, IsPlaceOver (Bq j) (w j)) → (∀ j, IsPlaceOver (Bq j) (v j)) →
    (∀ j, Dec (F := Lp L) (Bq j) ≤ (resP L Ω).range) → ∃ A : LevMod b h w, A.ClassicalAlt
variable {c : Coef l} {n : ℕ} {r : Resid V0.frame c.O n} (B : UniversalOrdinaryDeterminantRing r)
def LevelIdealCondition (J : Ideal B.B) : Prop :=
  ∃ b : TWBase (pairOf B.u) J Empty (n * Module.finrank ℚ (Lp L)), _root_.UpperTheory.V.Th.LevelAtOrdinaryDeterminantRing b ∧ (∀ k, b.wt.γ k ∈ V0.frame.Iv (b.wt.v k)) ∧
    ∀ (x : B.B →ₐ[c.O] c.O) (h : s.Wt n), (barPt B x).Arith h → CtrlH b x
end Ar
def HidaFamilyCondition : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → ∀ (c : Coef l) (n : ℕ), 1 ≤ n →
    ∀ (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (ι : Qbar l ≃+* ℂ), ∃ J : Ideal B.B, B.PointTheoremBaseObject ι J ∧ _root_.UpperTheory.V.Th.LevelIdealCondition B J
def HasHeckeOperatorDense : Prop :=
  _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ)
    (b : TWBase (pairOf B.u) J Empty D), _root_.UpperTheory.V.Th.LevelAtOrdinaryDeterminantRing b → ∀ T : TWGrp (globOf r V0), TWPl r T → OpAt b T
def OrdinaryMainCase : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V0.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B)
    (y : Pt (globOf r V0).frame c.O n) (x : B.B →ₐ[c.O] c.O) (h : s.Wt n) (q : ℕ) (sg : Fin q → V0.frame.G₀)
    (al : Fin q → Fin n → c.O), V0.S' = s.S → 1 ≤ n → _root_.UpperTheory.V.Th.LevelIdealCondition B J → J ≤ RingHom.ker x → (barPt B x).Arith h →
    B.u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ → y.N4 V0.frame.D0 →
    (∀ j, sg j ∈ V0.frame.G' ∧ Function.Injective (al j) ∧
      (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))) →
    DetQ (globOf r V0).frame c.O (pushRep (algebraMap c.O (Qbar l)) y.ρ)
      (GeneralLinearGroup.map (algebraMap c.O (Qbar l)) y.P) (Set.range sg) →
    ∀ δ : B.B →ₗ[c.O] c.O, IsDer x δ → (∀ v i, ∀ g ∈ V0.frame.Iv v, δ (B.u.ψ v i g : B.Bˣ) = 0) →
      ∀ g, δ (B.u.D.tr (MonoidAlgebra.single g 1)) = 0
end UpperTheory.V.Th
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWinPm
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.V.Ws.pmPur_w_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
        T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
        ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → PureW ι r := by
  intro hU Ω _ _ _ l _ c D T hT _ c' h K X B Λ ι J₀ hM φ hφ J hJ y hy hw r hr
  have hD : D.Good := hT.2.elim (fun a => a.1.1) fun a => a.1.1
  obtain ⟨wt, hwt⟩ := Pu.arith hU.pr.litN.aut.art K X B φ y hD hφ hw
  obtain ⟨ρ, -, hss, hρ, a, d, m, ρ', hd, hcp, hpure⟩ := _root_.UpperTheory.GalN.V.end1W' hM.end1 _ wt (K.le_ker_pt φ y J₀ (hJ ▸ hy)) hwt
  have hm := Pu.mOne c' ρ _ (chiO T.L Ω l c'.O) (cycBar T.L Ω l) (Pu.ptRed K.V B _ ρ hρ) rfl (Pu.noOm K hD hT.1) a d m ρ'
    (fun i => ⟨(hd i).1, (hd i).2.1⟩) hcp
  obtain ⟨Z, hZ, hZ'⟩ := Pu.levFin K.V
  refine Pu.pureOf_w ι T.L r ρ K.kapQ _ (hZ.union (Filter.eventually_cofinite.1 (hpure hm))) (fun g => ?_) fun w hw0 => ?_
  · rw [Pu.ptCp K X B φ y ρ hφ hρ g, ← hr]
    rfl
  · have hw : w ∉ Z := fun k => hw0 (Or.inl k)
    have hw' := not_not.1 fun k => hw0 (Or.inr k)
    obtain ⟨b, hb⟩ := Pu.frobEigEx ι ρ w fun A hA s hs => Pu.repKill K.V B _ ρ hρ hss s ((hZ' w hw).2 A hA s hs)
    exact Pu.frobAbs_w ι ρ w b hb (hw' b hb)
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
section SlopeTestRemainingChoices
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
end SlopeTestRemainingChoices
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
private theorem span_of_equiv {K K' H n : Type} [CommRing K] [CommRing K'] [Fintype n] [DecidableEq n] (e : K ≃+* K')
    (f : H → Matrix n n K) (f' : H → Matrix n n K') (hf : ∀ g i j, f' g i j = e (f g i j))
    (h : Submodule.span K' (Set.range f') = ⊤) : Submodule.span K (Set.range f) = ⊤ := by
  have key : ∀ x ∈ Submodule.span K' (Set.range f'), x.map e.symm ∈ Submodule.span K (Set.range f) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨g, rfl⟩ := ha
      refine Submodule.subset_span ⟨g, ?_⟩
      ext i j
      simp [hf]
    | zero =>
      have : (0 : Matrix n n K').map e.symm = 0 := by ext i j; simp
      rw [this]; exact zero_mem _
    | add a b _ _ ha hb =>
      have : (a + b).map e.symm = a.map e.symm + b.map e.symm := by ext i j; simp
      rw [this]; exact add_mem ha hb
    | smul s a _ ha =>
      have : (s • a).map e.symm = e.symm s • a.map e.symm := by ext i j; simp
      rw [this]; exact Submodule.smul_mem _ _ ha
  rw [eq_top_iff]
  intro y _
  have h1 := key (y.map e) (by rw [h]; trivial)
  have h2 : (y.map e).map e.symm = y := by ext i j; simp
  rwa [h2] at h1
private theorem charpoly_mapRep {R R' H : Type} [CommRing R] [CommRing R'] [Group H] (f : R →+* R') (r r' : H →* M4 R)
    (h : ∀ g, (r g).charpoly = (r' g).charpoly) (g : H) : (mapRep f r g).charpoly = (mapRep f r' g).charpoly := by
  change ((r g).map f).charpoly = ((r' g).map f).charpoly
  rw [Matrix.charpoly_map, Matrix.charpoly_map, h]
theorem UpperTheory.V.Ws.fin0_no_end_all_irr_of_good_con_purity_aut :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ ι : PadicAlgCl l ≃+* ℂ, Con D → _root_.UpperTheory.V.Ws.PurityAtPoints D ι → _root_.UpperTheory.V.Ws.AutmAlt D ι → D.Fin0 ∧ D.NoEnd ∧ D.AllIrr (_root_.UpperTheory.V.Aut.IsAut4Alt ι) := by
  intro hP Ω _ _ _ l _ c D hD ι hC hPu hA
  obtain ⟨⟨𝔟, e, he⟩, -⟩ := ambZero l
  refine ⟨?_, ?_, ?_⟩
  · by_contra hF
    obtain ⟨𝔞, r, hch, hr, x, hx, hne⟩ := ptOver hP D hD hF
    obtain ⟨u, hu⟩ := ptPair hP D hD 𝔞 r hr
    rcases triV hP D hD 𝔞 r hr with h | h | ⟨h02, h20, h⟩
    · exact hC 𝔞 hch r u hu (Or.inl h)
    · obtain ⟨n, hn, hxn⟩ := diagConst D hD 𝔞 hch r hr u hu h x hx
      exact hne n hn hxn
    · obtain ⟨r₁, u₁, hu₁, hb, hs⟩ := blockPart D hD 𝔞 r hr u hu h02 h20 h
      obtain ⟨r₂, u₂, hu₂, hE, -⟩ := bl hP D hD 𝔞 r₁ u₁ hu₁ hb hs
      exact hC 𝔞 hch r₂ u₂ hu₂ (Or.inr hE)
  · intro r hr hb hs
    obtain ⟨r', hr', rfl⟩ := eptV D hD 𝔟 e he r hr
    obtain ⟨u, hu⟩ := ptPair hP D hD 𝔟 r' hr'
    have hb' : ∀ g, IsBlock (r' g) := fun g i j hij =>
      Subtype.ext (e.injective ((hb g i j hij).trans (map_zero e).symm))
    have hs' := span_of_equiv e (fun g => (mapRep 𝔟.toK r' g).submatrix ixA ixA) _ (fun _ _ _ => rfl) hs
    obtain ⟨r₂, u₂, hu₂, hE, hcp⟩ := bl hP D hD 𝔟 r' u hu hb' hs'
    refine nePure_w D hD ι 𝔟 e he r' u hu hb' ?_
    obtain ⟨H, M, hH, hM, h⟩ := _root_.UpperTheory.GalN.V.pureW' (hPu 𝔟 e he r₂ u₂ hu₂ (Or.inr hE))
    have hc := charpoly_mapRep ((e : 𝔟.K →+* PadicAlgCl l).comp 𝔟.toK) r₂ r' hcp
    refine ⟨H, M, hH, hM, fun p hp hpM A hA f σ hf hσ hF => ?_⟩
    rw [← hc]
    exact h p hp hpM A hA f σ hf hσ hF
  · intro r hr hI
    obtain ⟨r', hr', rfl⟩ := eptV D hD 𝔟 e he r hr
    obtain ⟨u, hu⟩ := ptPair hP D hD 𝔟 r' hr'
    exact hA 𝔟 e he r' u hu (span_of_equiv e (mapRep 𝔟.toK r') _ (fun _ _ _ => rfl) hI)
end
end
end

