module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameOfRealizationModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1348
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1340
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoprimeScalarForEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

theorem pairL_levRep_zsmul {n : ℕ} (x : Fin n → Dw.La) (m : ℤ) (q : Fin n → LevQ Dw l) :
    (l.M : ℤ) ∣ pairL (l := l) x (fun b => levRep ((m • q) b)) - m * pairL (l := l) x (fun b => levRep (q b)) := by
  have hrep : ∀ q : LevQ Dw l, (Submodule.Quotient.mk (levRep q) : LevQ Dw l) = q := fun q =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  have e : m * pairL (l := l) x (fun b => levRep (q b)) = pairL (l := l) x (fun b => m • levRep (q b)) := by
    unfold pairL
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_comm, map_zsmul, smul_eq_mul]
  rw [e]
  refine GlobalTheory.LevelPairing.pairL_congr _ _ _ _ (fun b => by simp) fun b => ?_
  rw [← Submodule.Quotient.eq, hrep]
  refine Eq.trans ?_ (map_zsmul (Submodule.mkQ _) m (levRep (q b))).symm
  rw [Submodule.mkQ_apply, hrep, Pi.smul_apply]

theorem map_phiHat (c : Coeff l) (τ : c.F →+* ℂ) : ∃ m : ℤ, IsCoprime m (l.M : ℤ) ∧
    ∀ (n : ℕ) (φ : (Fin n → LevQc Dw l) → c.F), (∀ x, φ x = 0 ∨ φ x = 1) → ∀ q,
      τ (phiHat c φ q) = c.F.val.toRingHom (phiHat c φ (m • q)) := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  haveI : NeZero l.M := ⟨hM⟩
  have h0 := GlobalTheory.LevelPairing.zetaM_prim c
  have h1 : IsPrimitiveRoot (c.F.val.toRingHom (zetaM c)) l.M := h0.map_of_injective c.F.val.toRingHom.injective
  have h2 : IsPrimitiveRoot (τ (zetaM c)) l.M := h0.map_of_injective τ.injective
  obtain ⟨m, -, hm⟩ := h1.eq_pow_of_pow_eq_one h2.pow_eq_one
  have hc : m.Coprime l.M := (h1.pow_iff_coprime (Nat.pos_of_ne_zero hM) m).1 (hm ▸ h2)
  refine ⟨m, Nat.isCoprime_iff_coprime.2 hc, fun n φ hφ q => ?_⟩
  haveI := GlobalTheory.AdTh.PairModel.finite_levQc Dw l
  haveI := Fintype.ofFinite (Fin n → LevQc Dw l)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [phiHat, phiHat, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [GlobalTheory.LevelPairing.zpow_congr c (pairL_levRep_zsmul _ (m : ℤ) q), map_mul, map_mul, map_zpow₀, map_zpow₀, ← hm,
    _root_.zpow_mul, zpow_natCast]
  congr 1
  rcases hφ x with h | h <;> simp [h]

end Gen

end GlobalTheory.GalOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreDictionaryGoodAtGoodEmbedding
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem castDict_laws {D : D7} {V W : HSp D} (hV : V = W) {r : ℕ} (hr : W.rank = r) {Comp : Type}
    (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r)
    (mu : GA D V → ℂ) (Kf : Subgroup (GA D V)) (Kf' : Subgroup (GA D W))
    (hK : ∀ g : GA D W, g ∈ Kf' ↔ cast (congrArg (GA D) hV.symm) g ∈ Kf)
    (hu : ∃ th hr', (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr')
    (hm : ∃ hr' : V.rank = r, ∀ k, ModelW V hr' (X k)) (hmu : MuUnit V dict mu) (hc : Continuous mu) :
    (∃ th, (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif W (castDict hV dict) Kf' th hr) ∧
      (∀ k, ModelW W hr (X k)) ∧ MuUnit W (castDict hV dict) (castDict hV mu) ∧ Continuous (castDict hV mu) := by
  subst hV
  obtain rfl : Kf' = Kf := Subgroup.ext hK
  obtain ⟨th, hr', h1, h2⟩ := hu
  obtain ⟨hr'', h3⟩ := hm
  exact ⟨⟨th, h1, h2⟩, h3, hmu, hc⟩

theorem goodDict_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ w, WtIs (R.MW i σ) w → GoodDict R.θ (R.MW i σ) w (rank_Wc i) (T.U ((i : ℕ) + 1) (res T σ)).X (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ))) (T.cE ((i : ℕ) + 1) (res T σ)) (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hM h hpb i σ hσ hV w hw
  obtain ⟨hK, -, hfin, hopen⟩ := _root_.GlobalTheory.HolDict.PrincLev.principal_level D G Pl0 T0 A T R κ v₀ hL hM h hpb i σ hσ hV
  have hj : InR D ((i : ℕ) + 1) := inR i
  obtain ⟨h1, h2, h3, h4⟩ := castDict_laws hV (rank_Wc i) _ _ (T.mu ((i : ℕ) + 1) (res T σ)) _ _ hK
    (h.laws.dictU _ hj _ hσ) (h.laws.modelW _ hj _ hσ) (h.laws.muUnit _ hj _ hσ) (h.laws.muCont _ hj _ hσ)
  have hc : ∀ k, ‖T.cE ((i : ℕ) + 1) (res T σ) k‖ = 1 := h.laws.cUnit _ hj _ hσ
  exact
    { inf := hM.inf
      base := _root_.GlobalTheory.HolDict.BaseFrame.baseFrT_of_tieIn D G Pl0 T0 A T R κ v₀ hM h i σ hσ hV
      unif := h1
      model := h2
      muUnit := h3
      muCont := h4
      chi := h.laws.chiTriv _ hj _ hσ _ _ (dom_wtA (κ i))
      cNe := fun k h0 => by
        have := hc k
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      cBdd := ⟨1, fun k => (hc k).le⟩
      fin := @Finite.of_fintype _ (T.U ((i : ℕ) + 1) (res T σ)).fin
      levFin := hfin
      levOpen := hopen
      muK := _root_.GlobalTheory.HolDict.PrincLevChar.char_eq_one D G Pl0 T0 A T R κ v₀ hL hM h hpb i σ hσ hV
      wt := _root_.GlobalTheory.HolDict.extWt_eq_laU_add D G Pl0 T0 A T R κ v₀ hM h i σ hσ hV w hw }

end GlobalTheory.HolDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
section
noncomputable section

namespace GlobalTheory.FockKFin

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.EvAt0.PolD

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def dStep {κ : Type} [Fintype κ] (P : Submodule ℂ (SInf F κ)) : Submodule ℂ (SInf F κ) :=
  Submodule.span ℂ {h | ∃ a b : κ → mixedEmbedding.mixedSpace F, ∃ f ∈ P, h = dOp a b f}

theorem dOp_mem_dStep {κ : Type} [Fintype κ] (P : Submodule ℂ (SInf F κ)) (a b : κ → mixedEmbedding.mixedSpace F)
    {f : SInf F κ} (hf : f ∈ P) : dOp a b f ∈ dStep P :=
  Submodule.subset_span ⟨a, b, f, hf, rfl⟩

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def vacSp (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Submodule.span ℂ {g | GaussD M τ g}

def polLe (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (m : ℕ) :
    Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Nat.rec (motive := fun _ => Submodule ℂ (SInf F (Fin n × Fin d))) (vacSp M τ) (fun _ P => P ⊔ dStep P) m

theorem polLe_zero (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : polLe M τ 0 = vacSp M τ := rfl

theorem polLe_succ (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (m : ℕ) :
    polLe M τ (m + 1) = polLe M τ m ⊔ dStep (polLe M τ m) := rfl

theorem polLe_mono (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Monotone (polLe M τ) :=
  monotone_nat_of_le_succ fun m => by rw [polLe_succ]; exact le_sup_left

def pureL {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) : SInf F κ →ₗ[ℂ] (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end GlobalTheory.FockKFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxChangeRealisedCompAndReindex
section
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU.RealComp

variable {F : Type} [Field F] [NumberField F]

theorem isOp_comp {ψ : AddChar (AF F) ℂ} {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
    {t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)}
    {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}
    {T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)} {T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hs : IsOp ψ s S S') (ht : IsOp ψ t T T') : IsOp ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T') := by
  exact
    { pres φ h := ht.pres _ (hs.pres φ h)
      pres' φ h := hs.pres' _ (ht.pres' φ h)
      left φ h := by simp only [LinearMap.comp_apply]; rw [ht.left _ (hs.pres φ h), hs.left φ h]
      right φ h := by simp only [LinearMap.comp_apply]; rw [hs.right _ (ht.pres' φ h), ht.right φ h]
      adm l hl := by rw [← LinearMap.comp_assoc]; exact hs.adm _ (ht.adm l hl)
      adm' l hl := by rw [← LinearMap.comp_assoc]; exact ht.adm' _ (hs.adm' l hl)
      Heisenberg₂ w φ h := by
        simp only [LinearMap.comp_apply, Function.comp_apply]
        rw [hs.Heisenberg₂ w φ h, ht.Heisenberg₂ _ _ (hs.pres φ h)]
      theta := by
        obtain ⟨c₁, hc₁, e₁⟩ := hs.theta
        obtain ⟨c₂, hc₂, e₂⟩ := ht.theta
        exact ⟨c₂ * c₁, mul_ne_zero hc₂ hc₁, fun φ h => by
          simp only [LinearMap.comp_apply]; rw [e₂ _ (hs.pres φ h), e₁ φ h, mul_assoc]⟩
      norm μ μ'' hμ hμ'' := by
        letI : MeasurableSpace (κ' → AF F) := borel _
        haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
        haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
        obtain ⟨c₁, h1, h1', e₁⟩ := hs.norm μ Measure.addHaar hμ inferInstance
        obtain ⟨c₂, h2, h2', e₂⟩ := ht.norm Measure.addHaar μ'' inferInstance hμ''
        exact ⟨c₂ * c₁, mul_ne_zero h2 h1, ENNReal.mul_ne_top h2' h1', fun φ h => by
          simp only [LinearMap.comp_apply]; rw [e₂ _ (hs.pres φ h), e₁ φ h, mul_assoc]⟩ }

theorem dblAct_comp {κ κ' κ'' : Type} (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F))
    (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) :
    dblAct (t ∘ s) = dblAct t ∘ dblAct s := by
  funext w
  refine Prod.ext ?_ ?_ <;> funext a <;> rcases a with a | a <;> simp [dblAct]

end GlobalTheory.TowU.RealComp

namespace GlobalTheory.TowU.RealComp

open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

theorem isOp2_comp {ψ : AddChar (AF F) ℂ} {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
    {t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)}
    {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}
    {T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)} {T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hs : IsOp2 ψ s S S') (ht : IsOp2 ψ t T T') : IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T') := by
  obtain ⟨hs1, Sd, Sd', hsd, hsb⟩ := hs
  obtain ⟨ht1, Td, Td', htd, htb⟩ := ht
  have hc : ∀ {ι : Type} [Fintype ι], ∀ φ ∈ schA F ι, star φ ∈ schA F ι := fun φ h => GlobalTheory.ConjSch.conj_mem_schA φ h
  refine ⟨isOp_comp hs1 ht1, Td ∘ₗ Sd, Sd' ∘ₗ Td', ?_, fun φ₁ h₁ φ₂ h₂ => ?_⟩
  · rw [dblAct_comp]; exact isOp_comp hsd htd
  · simp only [LinearMap.comp_apply]
    rw [hsb φ₁ h₁ φ₂ h₂, htb _ (hs1.pres _ h₁) _ (hc _ (hs1.pres _ (hc _ h₂))), star_star]

variable {κ κ' : Type} [Fintype κ] [Fintype κ']

def addRe {X : Type} [TopologicalSpace X] [AddCommGroup X] (e : κ' ≃ κ) : (κ' → X) ≃ₜ+ (κ → X) where
  toFun x := x ∘ e.symm
  invFun y := y ∘ e
  left_inv x := by funext i; simp
  right_inv y := by funext i; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun i => continuous_apply _
  continuous_invFun := continuous_pi fun i => continuous_apply _

def reix {R : Type} (e : κ' ≃ κ) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ' → R) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x : κ' → R => x ∘ e.symm)

theorem reix_apply {R : Type} (e : κ' ≃ κ) (φ : (κ → R) → ℂ) (x : κ' → R) : reix e φ x = φ (x ∘ e.symm) := rfl

theorem reix_symm_reix {R : Type} (e : κ' ≃ κ) (φ : (κ → R) → ℂ) : reix e.symm (reix e φ) = φ := by
  funext x; simp only [reix_apply, Equiv.symm_symm]; congr 1; funext i; simp

def linRe (e : κ' ≃ κ) : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
  (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) e.symm).toContinuousLinearEquiv

theorem sb_reix (e : κ' ≃ κ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    (fun y : κ' → FiniteAdeleRing (𝓞 F) F => g (y ∘ e.symm)) ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F) :=
  ⟨hg.1.comp_continuous (addRe e).continuous, hg.2.comp_homeomorph (addRe e).toHomeomorph⟩

theorem reix_pureA (e : κ' ≃ κ) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    reix e (pureA F f g) = pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (linRe e) f)
      (fun y => g (y ∘ e.symm)) := by
  funext x
  rfl

theorem reix_mem_schA (e : κ' ≃ κ) {φ : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) : reix e φ ∈ schA F κ' := by
  have hle : schA F κ ≤ (schA F κ').comap (reix e) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    exact Submodule.subset_span ⟨_, _, sb_reix e hg, reix_pureA e f g⟩
  exact hle h

theorem reix_adm (e : κ' ≃ κ) {l : ((κ' → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ') :
    l ∘ₗ reix e ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl _ (sb_reix e hg)
  exact ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (linRe e)), fun f => by
    rw [LinearMap.comp_apply, reix_pureA]; exact hT _⟩

theorem reix_theta (e : κ' ≃ κ) (φ : (κ → AF F) → ℂ) : thetaSum F (reix e φ) = thetaSum F φ :=
  (Equiv.arrowCongr e (Equiv.refl F)).tsum_eq (fun ξ : κ → F => φ (fun i => algebraMap F (AF F) (ξ i)))

theorem reix_heis (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) (w : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ) :
    reix e (schr ψ w φ) = schr ψ (w.1 ∘ e, w.2 ∘ e) (reix e φ) := by
  have hd : ∀ u v : κ → AF F, (u ∘ e) ⬝ᵥ (v ∘ e) = u ⬝ᵥ v := fun u v => by
    simp only [dotProduct, Function.comp_apply]; exact Equiv.sum_comp e (fun i => u i * v i)
  funext x
  simp only [reix_apply, schr]
  have h1 : (x ∘ e.symm) ⬝ᵥ w.2 = x ⬝ᵥ (w.2 ∘ e) := by
    rw [← hd]; congr 1; funext i; simp
  have h2 : x ∘ e.symm + w.1 = (x + w.1 ∘ e) ∘ e.symm := by funext i; simp
  rw [h1, h2, hd]

theorem reix_norm (e : κ' ≃ κ) (μ : @Measure (κ → AF F) (borel _)) (μ' : @Measure (κ' → AF F) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (hμ' : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ') :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : (κ → AF F) → ℂ,
      ∫⁻ x, ‖reix e φ x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  letI : MeasurableSpace (κ → AF F) := borel _
  letI : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ
  haveI := hμ'
  let L : (κ' → AF F) ≃ₜ+ (κ → AF F) := addRe e
  haveI : (μ'.map L).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ' L
  have heq := Measure.isAddLeftInvariant_eq_smul (μ'.map L) μ
  refine ⟨(Measure.addHaarScalarFactor (μ'.map L) μ : ℝ≥0∞),
    ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', ENNReal.coe_ne_top,
    fun φ => ?_⟩
  have hm := lintegral_map_equiv (fun y => ‖φ y‖ₑ ^ 2) L.toHomeomorph.toMeasurableEquiv (μ := μ')
  have hL : (⇑L.toHomeomorph.toMeasurableEquiv : (κ' → AF F) → (κ → AF F)) = ⇑L := rfl
  rw [hL, heq, lintegral_smul_measure] at hm
  rw [ENNReal.smul_def, smul_eq_mul] at hm
  exact hm.symm

end GlobalTheory.TowU.RealComp

namespace GlobalTheory.TowU.RealComp

variable {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']

theorem isOp_reix (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) :
    IsOp ψ (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) (reix e) (reix e.symm) := by
  exact
    { pres _ h := reix_mem_schA e h
      pres' _ h := reix_mem_schA e.symm h
      left φ _ := reix_symm_reix e φ
      right φ _ := by simpa using reix_symm_reix e.symm φ
      adm _ hl := reix_adm e hl
      adm' _ hl := reix_adm e.symm hl
      Heisenberg₂ w φ _ := reix_heis ψ e w φ
      theta := ⟨1, one_ne_zero, fun φ _ => by rw [reix_theta, one_mul]⟩
      norm μ μ' hμ hμ' := by
        obtain ⟨c, h0, h1, h⟩ := reix_norm e μ μ' hμ hμ'
        exact ⟨c, h0, h1, fun φ _ => h φ⟩ }

theorem dblAct_reix (e : κ' ≃ κ) :
    dblAct (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) =
      fun w => (w.1 ∘ Equiv.sumCongr e e, w.2 ∘ Equiv.sumCongr e e) := by
  funext w
  refine Prod.ext ?_ ?_ <;> funext a <;> rcases a with a | a <;> simp [dblAct]

theorem isOp2_reix (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) :
    IsOp2 ψ (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) (reix e) (reix e.symm) := by
  refine ⟨isOp_reix ψ e, reix (Equiv.sumCongr e e), reix (Equiv.sumCongr e e).symm, ?_, fun φ₁ _ φ₂ _ => ?_⟩
  · rw [dblAct_reix]; exact isOp_reix ψ _
  · funext x
    simp only [reix_apply, boxFun, Pi.star_apply, star_star]
    congr 2 <;> funext i <;> simp

theorem realised_comp_reix : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ (κ κ' κ'' : Type) [Fintype κ] [Fintype κ'] [Fintype κ''] (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)) (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)) (T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsOp2 ψ s S S' → IsOp2 ψ t T T' → IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T')) ∧ ∀ (κ κ' : Type) [Fintype κ] [Fintype κ'] (e : κ' ≃ κ), ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (fun w => (w.1 ∘ e, w.2 ∘ e)) S S' :=
  fun _ _ _ ψ _ => ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ hs ht => isOp2_comp hs ht, fun _ _ _ _ e => ⟨_, _, isOp2_reix ψ e⟩⟩

end GlobalTheory.TowU.RealComp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRealFamilyArchimedeanLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.RealDirCoord

theorem continuous_ringEquiv_mixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

theorem eps_smul_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (z : AF F ⊗[F] E) :
    (pairA F 0 1) • z = LinearMap.rTensor E (LinearMap.inr F (Ainf F) (Af F))
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
    congr 1
    show ((0 : Ainf F) * a.1, (1 : Af F) * a.2) = ((0 : Ainf F), a.2)
    simp
  | add a b ha hb => rw [smul_add, ha, hb, map_add (f := _), map_add (f := _)]

theorem eps_smul_eq (D : D7) (z : AE D) :
    (pairA D.host.F 0 1) • z =
      LinearMap.rTensor D.host.E (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) (finPart D z) :=
  eps_smul_gen z

theorem eps_mul_snd {F : Type} [Field F] [NumberField F] (x : AF F) :
    (pairA F 0 1 * x).2 = x.2 := one_mul x.2

theorem darboux_real_coords : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ] (e : Formalism.IndefR.Datum.WO S T ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F)) (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.Datum.WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∃ P Q : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace D.host.F), ∀ t, e (L t) = (fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (P t i)) 0, fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (Q t i)) 0) := by
  intro D S T κ _ e k L hL hfin

  have hε : ∀ t, (pairA D.host.F 0 1) • L t = 0 := by
    intro t
    ext i j
    have h0 : finPart D (L t i j) = 0 := congrFun (congrFun (hfin t) i) j
    rw [Matrix.smul_apply, eps_smul_eq, h0, LinearMap.map_zero]
    rfl
  have hsnd : ∀ t i, ((e (L t)).1 i).2 = 0 ∧ ((e (L t)).2 i).2 = 0 := by
    intro t i
    have h := congrArg e (hε t)
    rw [LinearEquiv.map_smul, LinearEquiv.map_zero] at h
    have h1 := congrArg Prod.snd (congrFun (congrArg Prod.fst h) i)
    have h2 := congrArg Prod.snd (congrFun (congrArg Prod.snd h) i)
    exact ⟨(eps_mul_snd _).symm.trans h1, (eps_mul_snd _).symm.trans h2⟩

  have he : Continuous e := by
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    haveI : IsModuleTopology (AF D.host.F) (Formalism.IndefR.Datum.WO S T) :=
      inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin _ → Fin _ → AE D))
    exact IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc : ∀ (p : ((κ → AF D.host.F) × (κ → AF D.host.F)) → (κ → AF D.host.F)), Continuous p →
      (∀ x y, p (x + y) = p x + p y) →
      ∃ P : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace D.host.F),
        ∀ t i, P t i = InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (p (e (L t)) i).1 := by
    intro p hp hadd
    let f : (Fin k → ℝ) →+ (κ → mixedEmbedding.mixedSpace D.host.F) :=
      { toFun := fun t i => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (p (e (L t)) i).1
        map_zero' := by
          funext i
          have h0 : p 0 = 0 := by simpa using hadd 0 0
          rw [map_zero, LinearEquiv.map_zero, h0]
          exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F)
        map_add' := by
          intro a b
          funext i
          rw [map_add (f := _), LinearEquiv.map_add (e := _), hadd]
          exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F) _ _ }
    have hf : Continuous f := by
      refine continuous_pi fun i => ?_
      exact (continuous_ringEquiv_mixed D.host.F).comp
        (continuous_fst.comp ((continuous_apply i).comp (hp.comp (he.comp hL))))
    exact ⟨f.toRealLinearMap hf, fun t i => rfl⟩
  obtain ⟨P, hP⟩ := hc Prod.fst continuous_fst (fun _ _ => rfl)
  obtain ⟨Q, hQ⟩ := hc Prod.snd continuous_snd (fun _ _ => rfl)
  refine ⟨P, Q, fun t => ?_⟩
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · show (e (L t)).1 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (P t i), 0)
    rw [hP, RingEquiv.symm_apply_apply]
    exact Prod.ext rfl (hsnd t i).1
  · show (e (L t)).2 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (Q t i), 0)
    rw [hQ, RingEquiv.symm_apply_apply]
    exact Prod.ext rfl (hsnd t i).2

end GlobalTheory.RealDirCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_inverse_heckeTranslates_forget_level : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x, g (g' x) = k • x) → (∀ x, g' (g x) = k • x) → c * c' = k ^ 2 → ∀ (hc : (N * k * k).Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k * k) s) (o₁ : Obj b (N * k) s) (o₂ : Obj b N s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o₁.A ⟶ o₂.A), IsHecke g' c' k (N * k) o o₁ ψ₁ → IsHecke g c k N o₁ o₂ ψ₂ → Nonempty (ObjMap (o.forget N ⟨k * k, by ring⟩ hc) o₂ (𝟙 S)) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.Comp.nonempty_objMap_forget) | (exact GlobalTheory.UPel.HT.Hecke.Comp.nonempty_objMap_forget) | (intros; apply GlobalTheory.UPel.HT.Hecke.Comp.nonempty_objMap_forget <;> assumption)
end

