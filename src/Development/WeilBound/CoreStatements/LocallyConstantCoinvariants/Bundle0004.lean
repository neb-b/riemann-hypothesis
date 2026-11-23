module

public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0001
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoStatement
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfSurj
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ContinuousFinId
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictDef
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ActEEqOfConjRelated
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.HermitianCharacters.SelfDualLatticeFiltrationCharacter
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.WeilRepresentationThetaEquivariance
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.FullOfSoLoc
section
noncomputable section

namespace PositivityTheory.KCo

section Local

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

def augF (n d : ℕ) (ν α : kˣ →* ℂˣ) : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ) :=
  Submodule.span ℂ {z | ∃ g : GL (Fin n) k, ∃ Φ, Full Φ ∧ z = omB ν α g 1 Φ - Φ}

theorem augF_le {ν α : kˣ →* ℂˣ} : augF n d ν α ≤ aug n d ν α :=
  Submodule.span_mono fun _ ⟨g, Φ, h, e⟩ => ⟨g, Φ, h.1, e⟩

theorem irrF (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {ν α : kˣ →* ℂˣ} (hnd : n ≤ d) (hν : USm ν)
    (N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ)) (hA : aug n d ν α ≤ N)
    (hN : ∀ h : GL (Fin d) k, ∀ Φ ∈ N, Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) → omB ν α 1 h Φ ∈ N) :
    (∀ Φ, Full Φ → Φ ∈ N) ∨ ∀ Φ ∈ N, Full Φ → Φ ∈ augF n d ν α := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnd
  have hμ : IsSmoothChar ν⁻¹ := IsSmoothChar.inv hν.2
  obtain ⟨E⟩ := _root_.GlobalTheory.CompanionTheory.ThetaGLLen.fibStr k (Fin n) (Fin (n + t)) (Fin n) (Fin t) (stdSum rfl) n (Fintype.card_fin n).symm ν⁻¹ hμ
  have hR : twRel ((omegaOn (Fin n) (Fin (n + t)) ν⁻¹ {n}).comp (MonoidHom.inl _ _)) 1 ≤
      (augF n (n + t) ν α).comap extZ := Submodule.span_le.2 (by
    rintro _ ⟨g, φ, rfl⟩
    refine Submodule.subset_span ⟨g, extZ φ, ⟨extZ_mem φ, fun Y hY => extZ_neg φ (by rwa [rank_transpose])⟩, ?_⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    congr 1
    refine funext fun Y => (extZ_act _ g 1 φ Y).trans ?_
    have n1 : nabs k 1 = 1 := by simp [nabs]
    simp [omB, omChar, apow, val_absPow, n1])
  rcases irr_equiv E (irr_ind hB n t hμ (fun y => by simp [hν.1 y])) (N.comap extZ) (hR.trans (Submodule.comap_mono (augF_le.trans hA))) (by
    intro h φ hf
    have h1 := hN (invT h) _ hf (extZ_mem φ)
    rw [Submodule.mem_comap]
    have c0 : (α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Units.ne_zero (absPow k ((n : ℂ) / 2) (gdet (invT h))))
    convert N.smul_mem ((omChar (Fin n) (Fin (n + t)) ν⁻¹ (1, h) : ℂ) /
      ((α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2))) h1 using 1
    funext Y
    have e1 : omB ν α 1 (invT h) (extZ φ) Y = (α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2) *
        extZ φ ((1 : GL (Fin n) k).valᵀ * Y * (invT h).val) := by
      simp [omB, apow, nabs]
    rw [extZ_act, Pi.smul_apply, e1, smul_eq_mul, ← mul_assoc, div_mul_cancel₀ _ c0]) with h | h
  · refine Or.inl fun Φ hΦ => ?_
    obtain ⟨φ, rfl⟩ := exists_extZ hΦ
    exact (h ▸ Submodule.mem_top : φ ∈ N.comap extZ)
  · refine Or.inr fun Φ hm hΦ => ?_
    obtain ⟨φ, rfl⟩ := exists_extZ hΦ
    exact hR (h hm)

end Local

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem full_of_soLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (h : IsCMExt F E σ) (hψ : IsStd ψ)
    (hX : X.J.det ≠ 0) (hW : W.J.det ≠ 0) {t : E →ₐ[F] Fv F v} {ι} (hι : M.IsLinBar ψ t 1 1 ι) {φ} (hφ : φ ∈ M.SoLoc ψ t) :
    ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), Y.rank ≠ n → ι φ Y = 0 := by
  obtain ⟨h1, ι', hι', h2⟩ := hφ
  intro Y hY
  obtain ⟨x, hx, h0, rfl⟩ := exists_coB (X := X) (W := W) h t hX hW Y
  exact eigen_kill M h hψ hX hW hι' ((LinearMap.proj (coB σ X W t x)).comp ι) hx h0
    (fun u hu hu1 φ' h' => mult' M hψ hι hu hu1 hx h0 h') h1 (h2 _ hY)

theorem soCoinv_of (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (hD : DictSt) (hK : GlobalTheory.ThK.KFin) :
    PositivityTheory.ThKF.SoCoinv := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT φ hφ hA
  obtain ⟨Rf, hF⟩ := hK F E σ B a a' G X om om' hT
  have ha' : 1 ≤ a' := by have := hT.geo.aBig; omega
  obtain ⟨⟨ι, hι⟩, ν, α, hν, -, h1, hd⟩ := hD F E σ _ _ B G.V' G.W G.M' om' _ _ hT.base ⟨_, _, hT.geo.hV'⟩ ⟨_, _, hT.geo.hW⟩
    hT.geo.hM' hT.weil' hT.chars.heckeα (isHecke_div hT.chars.heckeα hT.chars.heckeβ) B.v₁ B.τ₁
  have hn := nu_statement F E σ B a a' G X om om' hT B.v₁ hT.chars.good
  have hν1 : ν ≠ 1 := fun e => (h1 ha' (by omega) e).elim (hn _) (hn _)
  have hD' := hd ι hι
  have hb := hι.bij
  have := hF.nontriv B.v₁
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdet : ∀ {m : ℕ} (J : Matrix (Fin m) (Fin m) E), (J.map (B.emb w).1).det ≠ 0 → J.det ≠ 0 := fun J hJ h0 =>
    hJ (((RingHom.map_det _ J).symm.trans (congrArg _ h0)).trans (map_zero _))
  have dX : G.V'.J.det ≠ 0 := hdet _ (GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hV'.sig w))
  have dW : G.W.J.det ≠ 0 := hdet _ fun h0 =>
    GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hW.sig w) (by rw [Matrix.det_smul, h0, mul_zero])
  have hs : φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁) := augAt_le hA
  have hf : Full (ι φ) := ⟨hb.1 hs, fun Y hY => by
    have : Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) ≤ LinearMap.ker ((LinearMap.proj Y).comp ι) :=
      Submodule.span_le.2 fun χ hχ => full_of_soLoc G.M' hT.base.cm hT.base.std dX dW hι hχ Y hY
    exact this hφ⟩
  rcases irrF hB (α := α) (by omega) hν ((SB _ ⊓ LinearMap.ker (Rf.p' B.v₁)).map ι)
    ((aug_le_map hb hD').trans (Submodule.map_mono (le_inf augAt_le (hF.inv' _)))) (by
      rintro h₀ _ ⟨ψ, hψ, rfl⟩ -
      obtain ⟨h, hh, hr⟩ := hD'.rightOnto h₀
      obtain ⟨ψ₁, h₁, ha, e⟩ := hr ψ hψ.1
      refine ⟨ψ₁, ⟨h₁, ?_⟩, e⟩
      have h0 : Rf.p' B.v₁ ψ = 0 := hψ.2
      simpa using (hF.equiv _ h hh 0 (zero_mem _) ψ hψ.1 0 (zero_mem _) ψ₁ h₁ (acts_zero _) ha (by simp [h0])).symm) with h | h
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (0 : Rf.Pi B.v₁)
    obtain ⟨ψ, hψ, rfl⟩ : x ∈ (SB _).map (Rf.p' B.v₁) := hF.onto' _ ▸ Submodule.mem_top
    obtain ⟨ψ₀, h₀, hf₀, ha⟩ := exists_full surjectivity_statement hb hD' hν hν1 hψ
    obtain ⟨χ, hχ, e⟩ := h _ hf₀
    have e' : χ = ψ₀ := hb.2.1 hχ.1 h₀ e
    have h2 : Rf.p' B.v₁ (ψ - ψ₀) = 0 := hF.inv' _ ha
    have h3 : Rf.p' B.v₁ ψ₀ = 0 := e' ▸ hχ.2
    exact hx (by rwa [map_sub, h3, sub_zero] at h2)
  · have key : augF a' (a + a') ν α ≤ (SB _ ⊓ PositivityTheory.ThKF.augOn om' B.v₁ (G.M'.SoLoc B.ψ B.τ₁)).map ι := Submodule.span_le.2 (by
      rintro _ ⟨g₀, Φ, hΦ, rfl⟩
      obtain ⟨χ, hχ, rfl⟩ := hb.2.2 hΦ.1
      obtain ⟨g, hg, hr⟩ := hD'.leftOnto g₀
      obtain ⟨χ₁, h₁, ha, e⟩ := hr χ hχ
      exact ⟨χ₁ - χ, ⟨sub_mem h₁ hχ, Submodule.subset_span ⟨g, hg, χ, ⟨hχ, ι, hι, hΦ.2⟩, χ₁, h₁, ha, rfl⟩⟩, by rw [map_sub, e]⟩)
    obtain ⟨χ, hχ, e⟩ := key (h _ ⟨φ, ⟨hs, hF.inv' _ hA⟩, rfl⟩ hf)
    rw [← hb.2.1 hχ.1 hs e]
    exact hχ.2

end PositivityTheory.KCo
end
end

-- bundled from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictAd
section
noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open PositivityTheory.Member.ZakTransform GlobalTheory.CompanionTheory.Ar.SvN GlobalTheory.EmbChart

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {v : Pl F}

theorem schr_inst (ψ : AddChar (Fv F v) ℂ) :
    @schr _ _ (invTwo v) ψ κ _ = @schr _ _ (invTwoV (v := v)) ψ κ _ := by
  rw [Subsingleton.elim (invTwo v) invTwoV]

theorem ad_heis (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) (hw : At (evFin F v) w) (φ : (κ → Fv F v) → ℂ) :
    Acts (evFin F v) (schr ψ w) φ (@schr _ _ (invTwo v) (psiV ψ v) κ _ (locW v w) φ) := by
  intro r hr
  rw [schr_inst, schr_tens ψ _ _ (indep_of hr.1), offP_eq, sub_smul, (at_iff _).1 hw, one_smul, sub_self, schr_zero]
  rfl

theorem ad_rest (r : (κ → AF F) → ℂ) (φ₀ : (κ → Fv F v) → ℂ) (hne : φ₀ ≠ 0) (hr : Rest (evFin F v) φ₀ r)
    (φ : (κ → Fv F v) → ℂ) (hφ : φ ∈ SB (κ → Fv F v)) : Rest (evFin F v) φ r := by
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hne
  let S : Module.End ℂ ((κ → Fv F v) → ℂ) := (LinearMap.proj y : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ).smulRight ((φ₀ y)⁻¹ • φ)
  have h := lift_mem (v := v) (S := S) (fun θ _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hφ)) hr.2
  rw [lift_tens _ _ (indep_of hr.1)] at h
  have e : S φ₀ = φ := by
    change φ₀ y • (φ₀ y)⁻¹ • φ = φ
    rw [smul_smul, mul_inv_cancel₀ hy, one_smul]
  exact ⟨hr.1, e ▸ h⟩

theorem ad_act (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (s : (κ → AF F) × (κ → AF F) → (κ → AF F) × (κ → AF F))
    (L L' : Module.End ℂ ((κ → Fv F v) → ℂ)) (sv : (κ → Fv F v) × (κ → Fv F v) → (κ → Fv F v) × (κ → Fv F v))
    (h1 : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) (h2 : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ)
    (h3 : ∀ w, ∀ Φ ∈ schA F κ, T (schr ψ w Φ) = schr ψ (s w) (T Φ))
    (h4 : ∀ φ ∈ SB (κ → Fv F v), L φ ∈ SB (κ → Fv F v) ∧ L' φ ∈ SB (κ → Fv F v) ∧ L' (L φ) = φ ∧ L (L' φ) = φ)
    (h5 : ∀ w, ∀ φ ∈ SB (κ → Fv F v), L (@schr _ _ (invTwo v) (psiV ψ v) κ _ w φ) =
      @schr _ _ (invTwo v) (psiV ψ v) κ _ (sv w) (L φ))
    (h6 : ∀ w, locW v (s w) = sv (locW v w) ∧ At (evFin F v) (s w - w)) :
    ∃ c : ℂ, ∀ φ ∈ SB (κ → Fv F v), Acts (evFin F v) T φ (c • L φ) := by
  have hA := isCharAF_of_isStd hψ
  have hc : Continuous (psv v ψ) := hA.1.comp cont_at
  rw [schr_inst] at h5
  have hL' : ∀ φ ∈ SB (κ → Fv F v), L' φ ∈ SB (κ → Fv F v) := fun φ h => (h4 φ h).2.1
  obtain ⟨x₀, hx₀⟩ := hA.2.2.2
  obtain ⟨a, ha⟩ := GlobalTheory.CompanionTheory.AdelicSchur.schur F κ ψ hA.1 (fun e => hx₀ (by rw [e]; rfl)) hA.2.2.1 (lift v L' * T)
    (fun Φ hΦ => lift_mem hL' (h1 Φ hΦ)) (fun l hl => h2 _ (lift_adm hL' l hl)) fun w Φ hΦ => by
      rw [Module.End.mul_apply, Module.End.mul_apply, h3 w Φ hΦ]
      refine lift_schr ψ ?_ (fun φ hφ => ?_) (h1 Φ hΦ)
      · rw [offP_eq, offP_eq, ← sub_eq_zero, ← smul_sub, sub_smul, one_smul, (at_iff _).1 (h6 w).2, sub_self]
      · have e := h5 (evP v w) _ (hL' φ hφ)
        rw [(h4 φ hφ).2.2.2] at e
        have e2 : evP v (s w) = sv (evP v w) := (h6 w).1
        rw [e2]
        exact (congrArg L' e).symm.trans (h4 _ (schr_mem_SB hc _ (hL' φ hφ))).2.2.1
  refine ⟨a, fun φ hφ r hr => ?_⟩
  have e := congrArg (lift v L) (ha _ hr.2)
  rw [Module.End.mul_apply, lift_lift (S'' := 1) hL' (fun θ h => (h4 θ h).2.2.2) (h1 _ hr.2), lift_one, map_smul,
    lift_tens _ _ (indep_of hr.1)] at e
  rw [e]
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem indep_at {r : (κ → AF F) → ℂ} (h : Indep v r) (x z : κ → AF F) (hz : At (evFin F v) z) : r (x + z) = r x := by
  have e : z = fun i => atPlace v (evFin F v (z i)) := funext fun i => by
    rw [← ep_mul]; exact (congrFun ((at_iff z).1 hz) i).symm
  rw [e]; exact h x _

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

open GlobalTheory.DiagForm Classical in
theorem lDiag_box_ne : ∃ f : SInf F κ, lDiag F κ (boxFun (pure f (stdF κ)) (pure f (stdF κ))) ≠ 0 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport fun x => (b x : ℂ) := b.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  let f : SInf F κ := h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  refine ⟨f, ?_⟩
  have hm := pure_mem f (good_std (F := F) (κ := κ))
  have hg := pf_mem (good_std (F := F) (κ := κ))
  set g := pf (stdF (F := F) κ) with hgd
  have g01 : ∀ y, g y = 0 ∨ g y = 1 := fun y => by
    obtain ⟨S, hS⟩ := exists_fin (good_std (F := F) (κ := κ)).2 y
    rw [hgd, pf_eq_prod S y hS]
    refine Finset.prod_induction _ (fun z : ℂ => z = 0 ∨ z = 1) ?_ (Or.inr rfl) fun u _ => ?_
    · rintro a c (rfl | rfl) (rfl | rfl) <;> simp
    · simp only [stdF, Set.indicator_apply]
      split_ifs <;> simp
  have g0 : g 0 = 1 := by
    rw [hgd, pf, finprod_eq_one_of_forall_eq_one]
    intro u
    simp [stdF, Set.indicator_apply]
  have e : resD F κ (boxFun (pure f (stdF κ)) (pure f (stdF κ))) =
      fun p => (((b (eI F κ p.1)) ^ 2 : ℝ) : ℂ) * ((‖g p.2‖ : ℝ) : ℂ) := funext fun p => by
    have e1 : pure f (stdF κ) (glue p) = (b (eI F κ p.1) : ℂ) * g p.2 := by
      change f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _)) * g p.2 = _
      simp only [RingEquiv.apply_symm_apply]
      rfl
    change pure f (stdF κ) (glue p) * pure f (stdF κ) (glue p) = _
    rw [e1]
    rcases g01 p.2 with h | h <;> simp [h, sq]
  rw [lDiag, LinearMap.comp_apply, Lext_apply _ (integrable_resD (GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ hm _ hm)), e, mu,
    integral_prod_mul (fun u => (((b (eI F κ u)) ^ 2 : ℝ) : ℂ)) (fun y => ((‖g y‖ : ℝ) : ℂ)), integral_complex_ofReal,
    integral_complex_ofReal]
  refine mul_ne_zero (Complex.ofReal_ne_zero.2 (ne_of_gt ?_)) (Complex.ofReal_ne_zero.2 (ne_of_gt ?_))
  · refine ((b.continuous.comp (eI F κ).continuous).pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      ?_ (fun u => sq_nonneg _) ?_
    · exact (b.hasCompactSupport.comp_homeomorph (eI F κ).toHomeomorph).comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    · simp only [Function.comp_apply, map_zero]
      rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
      simp
  · exact hg.1.continuous.norm.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) hg.2.norm
      (fun _ => norm_nonneg _) (by simp [g0])

open Classical in
theorem adjoint_statement : AdSt := by
  refine {
    psi := ?_
    Heisenberg₂ := fun F _ _ κ _ ψ v w hw φ => ad_heis ψ w hw φ
    rest := fun F _ _ κ _ v r φ₀ _ hne hr φ hφ => ad_rest r φ₀ hne hr φ hφ
    act := fun F _ _ κ _ ψ hψ v T s L L' sv => ad_act ψ hψ T s L L' sv
    diag := ?_ }
  · intro F _ _ ψ h
    have hA := isCharAF_of_isStd h
    obtain ⟨x₀, hx₀⟩ := hA.2.2.2
    refine ⟨fun e => hx₀ (by rw [e]; rfl), fun v => ⟨hA.1.comp cont_at, fun e => ?_⟩⟩
    obtain ⟨y, hy⟩ := ((GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hA).1 v).2
    exact hy (DFunLike.congr_fun e y)
  · intro F _ _ κ _ ψ v
    obtain ⟨f, hf⟩ := lDiag_box_ne (F := F) (κ := κ)
    have hi := indep_pure (v := v) f (stdF (F := F) κ)
    have e : tens (evFin F v) (stdF κ v) (pure f (Function.update (stdF κ) v 1)) = pure f (stdF κ) := by
      rw [← pure_update f (good_std (F := F) (κ := κ)).2, Function.update_eq_self]
    have hm := pure_mem f (good_std (F := F) (κ := κ))
    refine ⟨_, GlobalTheory.DiagForm.lDiag_adm, fun x y Φ hΦ => GlobalTheory.DiagForm.lDiag_schr ψ x y hΦ, stdF κ v, stdF_mem v,
      pure f (Function.update (stdF κ) v 1), ⟨indep_at hi, e ▸ hm⟩, ⟨fun x z hz => ?_, ?_⟩, e ▸ hf⟩
    · have h1 := indep_at hi (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => funext fun i => congrFun (hz u hu) _
      have h2 := indep_at hi (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => funext fun i => congrFun (hz u hu) _
      exact congrArg₂ (· * ·) h1 h2
    · have := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ hm _ hm
      rw [← e] at this
      convert this using 1
      funext x
      exact mul_mul_mul_comm _ _ _ _

end PositivityTheory.KCo
end
end

