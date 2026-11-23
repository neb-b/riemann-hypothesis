module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaTildeHeckeCharSplitMulSignOfNormFormula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1735
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivariance
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolStabInf

open Formalism.BasicNotions.TH GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : piInf (τ w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) / (‖piInf (τ w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))‖ : ℂ) ≠ 0 := by
    have h0 : piInf (τ w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ≠ 0 := by
      intro e
      have := congrArg (piInf (τ w)) z.mul_inv
      rw [map_mul, e, zero_mul, map_one] at this
      exact zero_ne_one this
    exact div_ne_zero h0 (by exact_mod_cast norm_ne_zero_iff.2 h0)
  rw [zpow_sub₀ this]

theorem locFin_fock1 (P Q R S : ℕ) (X : Mat P Q) (hX : IsKC X) (c : ℂ) :
    LocFin (fockAct1 P Q R S X + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).1 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs X hX y hy) (W.smul_mem c hy)⟩

theorem locFin_fock2 (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩


open scoped Classical in
theorem polStab : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    (∀ γ ∈ Lines σ G.V, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ G.M.Pol B.ψ B.emb) ∧
    (∀ k ∈ KInf σ G.V B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ G.M.Pol B.ψ B.emb) ∧
    (∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ f₂ : SInf F (Fin a × Fin (a + a')),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₂ → f₂ = f₁) ∧
    (∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb,
      Acts (evI F) (om (1, k)) f f₁ ∧ ∀ f₂ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, k)) f f₂ → f₂ = f₁) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' h
  obtain ⟨hb, hg, hc, hw, -⟩ := h
  choose A hA hAθ using fun w => _root_.GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => _root_.GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hD := _root_.GlobalTheory.HeisDer.derEx
  have hvl := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hD
  have hfe := _root_.GlobalTheory.FockMapEx.fockEx_of_derEx hD
  have hsec := _root_.GlobalTheory.RealLift.LieSecondPf.lieSecond_of_lieScalar hK.base hD hfe hvl (_root_.GlobalTheory.LieScal.lieScalar hK.base hD hvl)
  have hfst := GlobalTheory.T.lieFirst_of_lieSecond' hsec
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hD hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr
    hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1
    hc.expβ
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expβ hc.expα)
  have hadm := fun g => (hwp.isUSplitting).adm g
  have hL := GlobalTheory.RealLift.actsLaws
  have mem : ∀ T, Φ T ∈ G.M.Pol B.ψ B.emb := fun T => hr ▸ LinearMap.mem_range_self Φ T
  have pol : ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ T, f = Φ T := fun f hf => by
    rw [← hr] at hf
    obtain ⟨T, rfl⟩ := hf
    exact ⟨T, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f₁ h1
    obtain ⟨T, rfl⟩ := pol f hf
    obtain ⟨Yg, -, hY⟩ := _root_.GlobalTheory.RealLiftGen.genEx F E σ (Fin a) _ _ B.emb (incM F G.V.J) 1 A hb.cm hA1 γ hγ
    have h2 := (hL F _ (Φ T) _ f₁).1 _ (fun t => map_zero _) (hW1 γ hγ Yg hY T)
    have e := (hL F _ (Φ T) _ f₁).2.2.1 _ h2 h1
    rw [← e]
    exact mem _
  · intro k hk f hf f₁ h1
    obtain ⟨T, rfl⟩ := pol f hf
    obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ (Fin a) _ _
      B.emb (incM F G.V.J) 1 A G.V.θ hb.cm hA1 hAθ k hk.1 hk.2
    obtain ⟨U, -, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F _ _ Φ _ ((om.comp (MonoidHom.inl _ _)).comp γ)
      (GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w => locFin_fock1 _ _ _ _ (Yg w) (hKC w) _) (fun t l hl => hadm _ l hl)
      (fun T => hW1 γ hγ Yg hgen T)
    have h2 := (hL F _ (Φ T) (Φ (U T)) f₁).2.1 _ (map_zero _) (hSA T)
    change Acts _ (om (MonoidHom.inl _ _ (γ (Multiplicative.ofAdd 1)))) _ _ at h2
    rw [hγ1] at h2
    have e := (hL F _ (Φ T) _ f₁).2.2.2.1 _ h2 h1
    rw [← e]
    exact mem _
  · intro γ hγ f hf
    obtain ⟨T, rfl⟩ := pol f hf
    obtain ⟨Yg, -, hY⟩ := _root_.GlobalTheory.RealLiftGen.genEx F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1 γ hγ
    have h2 := (hL F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW2 γ hγ Yg hY T)
    exact ⟨_, mem _, h2, fun f₂ h3 => (hL F _ (Φ T) _ _).2.2.1 _ h3 h2⟩
  · intro k hk f hf
    obtain ⟨T, rfl⟩ := pol f hf
    obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ
      (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C G.W.θ hb.cm hC1 hCθ k hk.1 hk.2
    obtain ⟨U, -, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F _ _ Φ _ ((om.comp (MonoidHom.inr _ _)).comp γ)
      (GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w => locFin_fock2 _ _ _ _ (Yg w) (hKC w) _) (fun t l hl => hadm _ l hl)
      (fun T => hW2 γ hγ Yg hgen T)
    have h2 := (hL F _ (Φ T) (Φ (U T)) (Φ (U T))).2.1 _ (map_zero _) (hSA T)
    change Acts _ (om (MonoidHom.inr _ _ (γ (Multiplicative.ofAdd 1)))) _ _ at h2
    rw [hγ1] at h2
    exact ⟨_, mem _, h2, fun f₂ h3 => (hL F _ (Φ T) _ _).2.2.2.1 _ h3 h2⟩

end GlobalTheory.PolStabInf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingAutFixingSmallFieldFixesDeltaValues
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.SeriesTie
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.JoinChr (IsPlIdem locE)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DeltaFixed

theorem aut_fixes_delta_values : ∀ {D : D7} (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (χ : HChar D.host.E),
    ChrEq (ρ.B i j b).de.chi χ → χ.ValuesIn 0 (embLL0 D) → ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (embLL0 D y) = embLL0 D y) →
    ∀ σ, τ (ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i))) =
      ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := by
  intro D ρ hρ i j b χ hχ hval τ hτ σ
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  set f : D.ntw.O0 i →+* ℂ := (ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)) with hf

  have hker : IsOpen (ψ.ker : Set (G D.host.E D.nd.Om)) := by
    cases b
    · have e : (ψ.ker : Set (G D.host.E D.nd.Om)) = ((D.ntw.delta i).ker : Set _) := by
        ext g
        simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
      rw [e]
      exact D.ntw.delta_open i
    · simpa [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt] using D.ntw.delta_open i

  have hram : ∀ v, v ∉ D.ntw.pD i → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ g ∈ Ine (F := D.host.E) A, ψ g = 1 := by
    intro v hv A hA g hg
    have h1 : D.ntw.delta i g = 1 := by
      by_contra h
      exact hv ((D.ntw.delta_ram i v A hA).1 ⟨g, hg, h⟩)
    cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, h1]

  haveI : Finite (G D.host.E D.nd.Om ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hker
  have hn : ψ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hpow : ∀ g, ψ g ^ ψ.ker.index = 1 := fun g => by
    rw [← map_pow]
    exact (MonoidHom.mem_ker).1 (Subgroup.pow_index_mem _ g)

  have hchi : ChrEq (charOf ρ.rc f ψ) χ := by
    have := hχ
    rw [hρ.delta i j b] at this
    exact this

  let r' : G D.host.E D.nd.Om →* ℂˣ := (Units.map f.toMonoidHom).comp ψ
  let r : G D.host.E D.nd.Om →* ℂˣ := (Units.map ((τ : ℂ →+* ℂ).comp f).toMonoidHom).comp ψ
  have hr' : Continuous r' := GlobalTheory.DeltaGal.continuous_comp_of_isOpen_ker ψ hker (Units.map f.toMonoidHom)
  have hr : Continuous r := GlobalTheory.DeltaGal.continuous_comp_of_isOpen_ker ψ hker (Units.map ((τ : ℂ →+* ℂ).comp f).toMonoidHom)
  have hart : IsGlobalArtin ρ.rc.art := hρ.rc.artin
  obtain ⟨_, _, _, _, hidem, _⟩ := GlobalTheory.EtaProduct.exists_ev D
  have key : r = r' := by
    refine GlobalTheory.GalChar.eq_of_frob hart hr hr' ?_
    have h1 := GlobalTheory.GalChar.unr_ae χ
    have h2 : ∀ᶠ v in Filter.cofinite, v ∉ D.ntw.pD i :=
      Filter.eventually_cofinite.2 (by simpa using (D.ntw.pD i).finite_toSet)
    filter_upwards [h1, h2] with v hunr hv A hA s hs

    obtain ⟨x0, hx0, hx0a⟩ := (hart.frob v A hA (toAb D.host.E D.nd.Om s⁻¹)).2 ⟨s, hs, rfl⟩

    set k := unif v
    have hk : IsUnifAt v (atFin v k) := unif_spec v
    have hu : IsUnitAt v (x0 * (atFin v k)⁻¹) := by
      unfold IsUnitAt
      unfold IsUnifAt at hx0 hk
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx0, hk]
      exact mul_inv_cancel₀ (by simp)
    obtain ⟨t, ht, hta⟩ := GlobalTheory.GalChar.exists_ine hart hA hu
    have hψt : ψ t = 1 := hram v hv A hA t ht

    obtain ⟨e, he⟩ := hidem v
    let xe : (Formalism.L2.Theta.AE D)ˣ := (Formalism.L2.JoinChr.isUnit_locE he.1 k).unit
    have hxe : ρ.rc.sym xe = toAb D.host.E D.nd.Om (t⁻¹ * s⁻¹) := by
      have e1 : Units.map ρ.rc.κ.toMonoidHom xe = Neutral.B1.localIdele D.host.E v (atFin v k) := by
        apply Units.ext
        exact hρ.rc.loc v e he k
      have e2 : atFin v k = (x0 * (atFin v k)⁻¹)⁻¹ * x0 := by group
      change ρ.rc.art (Units.map ρ.rc.κ.toMonoidHom xe) = _
      rw [e1, e2, map_mul, map_mul, map_inv, map_inv, hta, hx0a, ← map_inv, ← map_mul]
    have hc := charOf_eq ρ.rc f hker hxe hn (hpow _)
    have hc2 := hchi.2 v e he k xe rfl
    have hloc : χ.locK v k = χ.val v := χ.val_eq hunr _ hk
    obtain ⟨y, hy⟩ := hval v hunr
    have hy' : embLL0 D y = ((χ.val v : ℂˣ) : ℂ) := by
      rw [hy, HChar.valTw]
      simp
    have hfs : f ((ψ s : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = embLL0 D y⁻¹ := by
      have h3 : f ((ψ (t⁻¹ * s⁻¹) : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = embLL0 D y := by
        rw [← hc, hc2, hloc, hy']
      rw [map_mul, map_inv, map_inv, hψt, inv_one, one_mul, map_units_inv] at h3
      rw [map_inv₀, ← h3, inv_inv]
    apply Units.ext
    show τ (f ((ψ s : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) = f ((ψ s : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)
    rw [hfs]
    exact hτ _
  have := congrArg (fun φ : G D.host.E D.nd.Om →* ℂˣ => ((φ σ : ℂˣ) : ℂ)) key
  exact this

end GlobalTheory.DeltaFixed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowCharacterTimesInverseUnitary
section
open NumberField

noncomputable section

namespace GlobalTheory.CovTop

open Formalism.L2.DIV

theorem prod_hom_pow_eq_one {H M ι : Type} [Group H] [CommMonoid M] (s : Finset ι) (f : ι → H →* M) (N : ℕ)
    (h : ∀ i x, f i x ^ N = 1) (x : H) : (∏ i ∈ s, f i) x ^ N = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have ih' : (∏ i ∈ s, f i x) ^ N = 1 := by simpa using ih
    simp [hi, mul_pow, h, ih']

theorem ofLocal_chi_pow {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    (Hl : (PP : Pg) → Subgroup (GL (Fin r) (kP PP.1))) (cl : (PP : Pg) → Hl PP →* LLˣ) (N : ℕ)
    (h : ∀ PP x, cl PP x ^ N = 1) (g : (LevelP.ofLocal Hl cl).H) : (LevelP.ofLocal Hl cl).chi g ^ N = 1 :=
  prod_hom_pow_eq_one (H := Subgroup.pi Set.univ Hl) Finset.univ _ N (fun PP x => h PP _) g

theorem unipotentTypeLevel_char_pow_eq_one {E : Type} [Field E] [NumberField E] {LL : Type} [CommRing LL] (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : (PP : Pl E) → AddChar (kP PP) LL) (N : ℕ) (hN : ∀ PP : Pg, (N : kP PP.1) = 0)
    (g : (P0 Pg r ψ).H) : (P0 Pg r ψ).chi g ^ N = 1 := by
  refine ofLocal_chi_pow _ _ N (fun PP x => ?_) g
  apply Units.ext
  simp only [addCharHom, Units.val_pow_eq_pow_val, MonoidHom.coe_toHomUnits, Units.val_one, MonoidHom.comp_apply,
    AddChar.toMonoidHom_apply]
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hN PP, zero_mul, AddChar.map_zero_eq_one]

theorem det_of_mem_unip {κ : Type} [CommRing κ] {r : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unip κ r) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
    Matrix.det_of_upperTriangular (fun i j hij => hg.1 hij)]
  exact Finset.prod_eq_one fun i _ => hg.2 i

variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

end GlobalTheory.CovTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem GlobalTheory.LinModelLocal.exists_omB_of_linBar : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (K : GL (Fin a') (Fv F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J),
    (∀ g, K g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp σ)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁) →
    ∀ (S : GL (Fin a') (Fv F Bs.v₁) → ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _, ∀ c : ℂ, S g (c • φ + φ') = c • S g φ + S g φ') →
    (∀ g g', ∀ φ ∈ GlobalTheory.WeilM.SB _, S (g * g') φ = S g (S g' φ)) →
    (∀ φ ∈ GlobalTheory.WeilM.SB _, S 1 φ = φ) →
    (∀ g (γ : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ)) (S g φ)) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin a' × Fin (a + a') → Fv F Bs.v₁) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∃ ν α : (Fv F Bs.v₁)ˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧
      ∀ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι → ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = omB ν α g 1 (ι φ) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hTr K hK S h1 hlin h2 h3 h4 h5
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := GlobalTheory.T.linearModel_heisenbergOperators_translation_char Bs Γ X om om' hTr K hK S h1 h4
  by_cases hex : ∃ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι
  swap
  · exact ⟨1, 1, fun x => by simp, fun ι hι => absurd ⟨ι, hι⟩ hex⟩
  obtain ⟨ι₀, hι₀⟩ := hex
  obtain ⟨hT0, hM0, hST0, hSM0⟩ := hA ι₀ hι₀
  have hbij0 := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι₀
  have hU0 : ∀ (w : (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)),
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁), GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) w φ ∈ GlobalTheory.WeilM.SB _ :=
    fun w => _root_.GlobalTheory.Adopt.schroedingerOperatorHeisenberg_preserves_schwartzBruhat (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc w
  have key1 : ∀ (h : GL (Fin a') (Fv F Bs.v₁)) (Y : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁)),
      h.valᵀ * (((h⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y) = Y := by
    intro h Y
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.one_mul]
  have key2 : ∀ (h : GL (Fin a') (Fv F Bs.v₁)) (Y : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁)),
      ((h⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * (h.valᵀ * Y) = Y := by
    intro h Y
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
  have hc : ∀ g : GL (Fin a') (Fv F Bs.v₁), ∃ c : ℂ, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁),
      (fun Y => ι₀ (S g φ) (((g⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y)) = c • ι₀ φ := by
    intro g
    refine _root_.GlobalTheory.LinSchur.eq_smul_of_commute (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁)) (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc hψ1 ι₀
      (fun φ Y => ι₀ (S g φ) (((g⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y)) hbij0 ?_
      (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C))
      (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l)) ?_ ?_
    · intro x hx y hy c
      funext Y
      simp only [hlin g x hx y hy c, map_add (f := _), map_smul, Pi.add_apply, Pi.smul_apply]
    · intro C x hx
      refine ⟨hU0 _ x hx, hT0 C x hx, ?_⟩
      funext Y
      simp only [hST0 g C x hx, Matrix.mul_add]
    · intro l x hx
      refine ⟨hU0 _ x hx, hM0 l x hx, ?_⟩
      funext Y
      simp only [hSM0 g l x hx, key1]
  choose c hc using hc
  have hrel : ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁),
      ι₀ (S g φ) = fun Y => c g * ι₀ φ (g.valᵀ * Y) := by
    intro g φ hφ
    funext Y
    have := congrFun (hc g φ hφ) (g.valᵀ * Y)
    simp only [key2, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hvac := (hTr.geo.hM'.vac Bs.v₁)
  set φv := Γ.M'.vac Bs.v₁
  have hφv : φv ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁) := hvac.1
  have hιv : ι₀ φv ≠ 0 := by
    intro h0
    exact hvac.2.1 (hbij0.injOn hφv (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.mp hιv
  have hmul : ∀ g g', c (g * g') = c g * c g' := by
    intro g g'
    have e := congrFun (congrArg ι₀ (h2 g g' φv hφv)) ((((g * g')⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y₀)
    rw [hrel (g * g') φv hφv, hrel g (S g' φv) (h1 g' φv hφv), hrel g' φv hφv] at e
    beta_reduce at e
    have e2 : (g'.val)ᵀ * ((g.val)ᵀ * ((((g * g')⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y₀)) = Y₀ := by
      rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, key1]
    rw [key1 (g * g') Y₀, e2] at e
    exact mul_right_cancel₀ hY₀ (e.trans (mul_assoc _ _ _).symm)
  have hone : c 1 = 1 := by
    have e := congrFun (congrArg ι₀ (h3 φv hφv)) Y₀
    rw [hrel _ _ hφv] at e
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul] at e
    exact (mul_eq_right₀ hY₀).mp e
  let cH : GL (Fin a') (Fv F Bs.v₁) →* ℂ := ⟨⟨c, hone⟩, hmul⟩
  have h2ne : (2 : Fv F Bs.v₁) ≠ 0 := (isUnit_of_invertible (2 : Fv F Bs.v₁)).ne_zero
  obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.ghom_factors_through_det h2ne cH.toHomUnits
  have hcχ : ∀ g, c g = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) := fun g => by
    rw [← hχ g]; rfl
  obtain ⟨ν, hν1, hν⟩ := _root_.GlobalTheory.HeisUnit.exists_unitary_factor (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc hψ1 ι₀ hbij0
    (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C))
    (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l))
    (fun C φ hφ => ⟨hU0 _ φ hφ, hT0 C φ hφ⟩) (fun l φ hφ => ⟨hU0 _ φ hφ, hM0 l φ hφ⟩)
    (fun μ hμ C φ _ φ' _ => _root_.GlobalTheory.schr_unitary _ hψc μ hμ _ φ φ') (fun μ hμ l φ _ φ' _ => _root_.GlobalTheory.schr_unitary _ hψc μ hμ _ φ φ')
    S h1 h5 χ (fun g φ hφ => by rw [hrel g φ hφ, hcχ g])
  refine ⟨ν, 1, hν1, ?_⟩
  intro ι hι g φ hφ
  obtain ⟨hT, hM, -, -⟩ := hA ι hι
  obtain ⟨c', hc'⟩ := _root_.GlobalTheory.LinSchur.eq_smul_of_commute (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁)) (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc hψ1 ι₀
    ι hbij0 (fun x _ y _ c => by rw [map_add (f := _), map_smul])
    (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C))
    (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l))
    (fun C x hx => ⟨hU0 _ x hx, hT0 C x hx, hT C x hx⟩) (fun l x hx => ⟨hU0 _ x hx, hM0 l x hx, hM l x hx⟩)
  rw [hc' _ (h1 g φ hφ), hc' φ hφ, hrel g φ hφ, hcχ g, hν g]
  funext Y
  simp only [omB, Pi.smul_apply, smul_eq_mul, map_one, Units.val_one, Matrix.mul_one, Fintype.card_fin, gdet,
    MonoidHom.one_apply, apow_one]
  push_cast
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareModelNegSpaceGoodSchroedingerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareModel_negSpace_goodSchroedinger : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW₁ G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (hJ : X.J = (-1 : D.host.E) • (spW₁ G i j).gram) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∃ co vac dom, Model.IsGood (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co vac ((M.ν (.grid (i : ℕ) (j : ℕ))).map (conjU _ (-1) hJ)) dom) B.ψ := by
  first | exact @GlobalTheory.FunObj.squareModelW₁_good | exact GlobalTheory.FunObj.squareModelW₁_good | (intros; apply GlobalTheory.FunObj.squareModelW₁_good <;> assumption)
end

