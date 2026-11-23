module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3125
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0106
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0074
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3126
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0095
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0107
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0053
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0091
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0092
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0103
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BaseSplitPrimeInLocalPlaces
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Helpers
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StageGeo
private theorem common_factor_of_pair_relation {T K : Type} [Group K] {t u : T} (ν : T → K →* Circle) (lam : T → ℂ) (h0 : ∀ s, lam s ≠ 0)
    (good : T → ℂ → Prop)
    (H : ∀ s₁ s₂ c₁ c₂, (s₁ = t ∨ s₁ = u) → (s₂ = t ∨ s₂ = u) → good s₁ c₁ → good s₂ c₂ →
      ∃ k, (ν s₂ k : ℂ) * c₁ * lam s₂ = (ν s₁ k : ℂ) * c₂ * lam s₁) :
    ∃ (κ : ℂ) (k : K), ∀ s c, (s = t ∨ s = u) → good s c → c = κ * ((ν s k : ℂ) * lam s) := by
  have same : ∀ s c₁ c₂, (s = t ∨ s = u) → good s c₁ → good s c₂ → c₁ = c₂ := fun s c₁ c₂ hs g₁ g₂ => by
    obtain ⟨k, hk⟩ := H s s c₁ c₂ hs hs g₁ g₂
    exact mul_left_cancel₀ (Circle.coe_ne_zero _) (mul_right_cancel₀ (h0 s) hk)
  have nz : ∀ s k, (ν s k : ℂ) * lam s ≠ 0 := fun s k => mul_ne_zero (Circle.coe_ne_zero _) (h0 s)
  by_cases ht : ∃ c, good t c
  · obtain ⟨c₁, g₁⟩ := ht
    by_cases hu : ∃ c, good u c
    · obtain ⟨c₂, g₂⟩ := hu
      obtain ⟨k, hk⟩ := H t u c₁ c₂ (.inl rfl) (.inr rfl) g₁ g₂
      refine ⟨c₁ / ((ν t k : ℂ) * lam t), k, ?_⟩
      rintro s c (rfl | rfl) g
      · rw [div_mul_cancel₀ _ (nz _ _)]
        exact same _ _ _ (.inl rfl) g g₁
      · rw [same _ _ _ (.inr rfl) g g₂, div_mul_eq_mul_div, eq_div_iff (nz _ _)]
        linear_combination -hk
    · refine ⟨c₁ / ((ν t 1 : ℂ) * lam t), 1, ?_⟩
      rintro s c (rfl | rfl) g
      · rw [div_mul_cancel₀ _ (nz _ _)]
        exact same _ _ _ (.inl rfl) g g₁
      · exact absurd ⟨c, g⟩ hu
  · by_cases hu : ∃ c, good u c
    · obtain ⟨c₂, g₂⟩ := hu
      refine ⟨c₂ / ((ν u 1 : ℂ) * lam u), 1, ?_⟩
      rintro s c (rfl | rfl) g
      · exact absurd ⟨c, g⟩ ht
      · rw [div_mul_cancel₀ _ (nz _ _)]
        exact same _ _ _ (.inr rfl) g g₂
    · refine ⟨0, 1, ?_⟩
      rintro s c (rfl | rfl) g
      · exact absurd ⟨c, g⟩ ht
      · exact absurd ⟨c, g⟩ hu
private theorem reSpace_eq_of_same {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {X Y : Spc F E n}
    (hJ : X.J = Y.J) (hL : X.L = Y.L) : reS X Y = Y := by
  cases X; cases Y; cases hJ; cases hL; rfl
theorem exists_pivot_pair {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} {a a' : ℕ}
    {Γ : Geo σ a a'} {Xa Xb : Chars F E} {oa oa' ob ob'} (ha : IsTriple B Γ Xa oa oa') (hb : IsTriple B Γ Xb ob ob') :
    ∃ R Ra Rb ca cb, IsMatched B Γ Xa oa oa' R Ra ∧ IsMatched B Γ Xb ob ob' R Rb ∧ IsConst B Γ Xa oa oa' R Ra ca ∧
      IsConst B Γ Xb ob ob' R Rb cb ∧ cb ≠ 0 := by
  obtain ⟨R, Ra, h1⟩ := hM F E σ B a a' Γ Xa oa oa' ha
  obtain ⟨R', Rb, h2⟩ := hM F E σ B a a' Γ Xb ob ob' hb
  have h3 : IsMatched B Γ Xb ob ob' R Rb := ⟨hb, _root_.GlobalTheory.T.characters_real_valued_of_equal_exponent hP F E σ B a a' Γ Xa Xb oa oa' ob ob' R ha hb h1.real, h2.fin⟩
  obtain ⟨⟨-, ⟨ca, hca, -⟩, -⟩, -⟩ := (hK.1 F E σ B a a' Γ Xa oa oa' ha).2 R Ra h1
  obtain ⟨⟨-, ⟨cb, hcb, -⟩, h0⟩, -⟩ := (hK.1 F E σ B a a' Γ Xb ob ob' hb).2 R Rb h3
  exact ⟨R, Ra, Rb, ca, cb, h1, h3, hca, hcb, h0 cb hcb⟩
variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
private theorem readings_of_split_units {G : GridData Lc sc} {μ₀ : T} (hL : Lc.Is μ₀) (i j : Fin D.R.m) (s : T) {Bs : Base D.host.F D.host.E}
    (hsub : (GlobalTheory.SqStep.chs G i j s).T ⊆ Bs.P)
    (hin : ∀ v : Bs.P, v.1 ∈ (GlobalTheory.SqStep.chs G i j s).T → GlobalTheory.AdelicU.splitPrime (Bs.τ v) ∈ locPl G s)
    (hU : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      GlobalTheory.AdelicU.splitPrime τ ∈ locPl G s → AUnit τ) :
    Reads (fun t => Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (fun _ => G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))
      (locPl G) Bs s (GlobalTheory.SqStep.chs G i j s) := by
  classical
  refine ⟨rfl, rfl, fun w => ⟨fun hw => ?_, ?_⟩, fun v hv => hU _ _ (hin v hv)⟩
  · have hv : w.under (𝓞 D.host.F) ∈ (GlobalTheory.SqStep.chs G i j s).T := by
      by_cases h0 : w ∈ G.pl.W0
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h0
        rw [G.pl.under_w hv]
        exact Finset.mem_union_left _ hv
      · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hw, h0⟩, rfl⟩)
    exact ⟨⟨_, hsub hv⟩, hv, GlobalTheory.FunObj.Good.under_injOn hL G s (hin ⟨_, hsub hv⟩ hv) hw (GlobalTheory.AdelicU.splitPrime_under _)⟩
  · rintro ⟨v, hv, rfl⟩
    exact hin v hv
private theorem base_split_prime_in_local_places {G : GridData Lc sc} {μ₀ : T} (hL : Lc.Is μ₀) {W : G.Weil} {i j : Fin D.R.m} {t : T}
    {Bs : Base D.host.F D.host.E} (hB : GlobalTheory.SqStep.BaseFits G W i j t Bs) (v : Bs.P) (hv : v.1 ∈ (GlobalTheory.SqStep.chs G i j μ₀).T) :
    GlobalTheory.AdelicU.splitPrime (Bs.τ v) ∈ locPl G μ₀ := by
  classical
  rw [GlobalTheory.SqStepArith.chs_T_base G hL i j] at hv
  have hw : G.pl.w v.1 ∈ G.pl.W0 := Finset.mem_image_of_mem _ hv
  have h1 := hB.2.2.2 v (Finset.mem_union_left _ hv)
  have e := GlobalTheory.FunObj.Good.under_injOn hL G t h1 (Finset.mem_union_left _ hw)
    ((GlobalTheory.AdelicU.splitPrime_under _).trans (G.pl.under_w hv).symm)
  rw [e]
  exact Finset.mem_union_left _ hw
private theorem stage_regular_geometry {ψ : AddChar (AF D.host.F) ℂ} {A A' WW : HSp D} {X : Tri T A A' WW} {FA : GlobalTheory.ChainFr.Fr A}
    {FA' : GlobalTheory.ChainFr.Fr A'} {FW : GlobalTheory.ChainFr.Fr WW} {hr : A.rank + A'.rank = WW.rank} {Bs : Base D.host.F D.host.E}
    {Γ Γ₀ : Geo D.sp.cm.sig A.rank A'.rank} (hO : GlobalTheory.SqStepBig.Over X Γ) (g : Γ.IsGood Bs) (g₀ : Γ₀.IsGood Bs)
    (ep : Γ₀.p = Γ.p) (eq : Γ₀.q = Γ.q) (h : IsStageGeo ψ X FA FA' FW hr Bs Γ₀)
    (JA : Γ.V.J = (1 : D.host.E) • A.gram) (JB : Γ.V'.J = (-1 : D.host.E) • A'.gram)
    (m1 : Γ.M.μ = X.m.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A 1 JA)) (d1 : Γ.M.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A 1 JA '' X.fd)
    (m2 : Γ.M'.μ = X.m'.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A' (-1) JB)) (d2 : Γ.M'.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A' (-1) JB '' X.fd') :
    (reG Γ Γ₀.V Γ₀.V' Γ₀.W).IsGood Bs ∧ IsStageGeo ψ X FA FA' FW hr Bs (reG Γ Γ₀.V Γ₀.V' Γ₀.W) := by
  obtain ⟨⟨r1, -, l1⟩, ⟨r2, -, l2⟩, r3, j3, l3⟩ := hO
  have L1 : Γ.V.L = Γ₀.V.L := Submodule.ext fun y => (l1 y).trans (h.latA.1 y).symm
  have L2 : Γ.V'.L = Γ₀.V'.L := Submodule.ext fun y => (l2 y).trans (h.latB.1 y).symm
  have L3 : Γ.W.L = Γ₀.W.L := Submodule.ext fun y => (l3 y).trans (h.latA.2 y).symm
  have J3 : Γ.W.J = Γ₀.W.J := j3.trans h.pairA.JW.symm
  have e1 : reS Γ.V Γ₀.V = Γ₀.V := reSpace_eq_of_same (JA.trans h.JA.symm) L1
  have e2 : reS Γ.V' Γ₀.V' = Γ₀.V' := reSpace_eq_of_same (JB.trans h.JB.symm) L2
  have e3 : reS Γ.W Γ₀.W = Γ₀.W := reSpace_eq_of_same J3 L3
  have hV : (reS Γ.V Γ₀.V).IsHerm D.sp.cm.sig Bs (A.rank - Γ.p) Γ.p := by rw [e1, ← ep]; exact g₀.hV
  have hV' : (reS Γ.V' Γ₀.V').IsHerm D.sp.cm.sig Bs Γ.q (A'.rank - Γ.q) := by rw [e2, ← eq]; exact g₀.hV'
  have hW : (reS Γ.W Γ₀.W).IsSkew D.sp.cm.sig Bs (A.rank + A'.rank - (Γ.p + Γ.q)) (Γ.p + Γ.q) := by
    rw [e3, ← ep, ← eq]; exact g₀.hW
  have G : (reG Γ Γ₀.V Γ₀.V' Γ₀.W).IsGood Bs :=
    ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hV, hV', hW, ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩,
      ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩
  refine ⟨G, ⟨h.pairA.base, h.pairA.psi, JA, J3.trans h.pairA.JW, ⟨_, _, hV⟩, ⟨_, _, hW⟩, G.hM⟩,
    ⟨h.pairB.base, h.pairB.psi, JB, J3.trans h.pairB.JW, ⟨_, _, hV'⟩, ⟨_, _, hW⟩, G.hM'⟩, ⟨l1, l3⟩, ⟨l2, l3⟩, h.cartA, h.cartB,
    JA, JB, m1, d1, m2, d2, h.basA, h.basB, h.basW⟩
end Helpers
theorem _root_.GlobalTheory.T.pivot_reduction_divisibility : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank),
        GlobalTheory.SqStepBig.Over X Γ → Γ.p = p → Γ.q = q → Γ.IsGood Bs →
        (∀ s, (s = t ∨ s = μ₀) → GlobalTheory.SqStepBig.Carried G W i j X Bs FA FA' FW Γ s) →
        ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank A'.rank) (P' : PolF D WW.rank A'.rank),
          (∀ s, (s = t ∨ s = μ₀) → ∀ h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ s P' h) X.fd' X.m') →
          ∃ (P : PolF D WW.rank A.rank) (k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))ˣ), ∀ s, (s = t ∨ s = μ₀) →
            ∀ om om' Rf (c : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf →
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf c →
              ∀ h, ((GlobalTheory.SqStep.chs G i j s).ν k : ℂ) * X.I W.ψ W.θ s P h = c * X.I' W.ψ W.θ s P' h := by
  intro hP hK hM
  obtain ⟨a1, h1⟩ := GlobalTheory.T.towerStage_seesawDictionary_framesSignatures
  obtain ⟨a2, h2⟩ := GlobalTheory.StageGeo.aUnit_locPl
  refine ⟨max a1 a2, fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, g1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨c2, x2, g2⟩ := h2 ε CF (le_of_max_le_right hCF)
  refine ⟨max c1 c2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  have q1 := g1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G
  have q2 := g2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G
  intro W hψ i j p q A A' WW X lam t Bs hX hF hB FA FA' FW Γ hO hp hq hg hs R P' hint
  obtain ⟨F₀, F₀', FW₀, a, b, -, -, -, hd⟩ := q1 W i j p q A A' WW X hX
  obtain ⟨-, -, -, -, nA, nA', nW, hXi⟩ := hX
  have b1 := hg.eBig
  have b2 := hg.aBig
  have b3 := hg.lt
  have b4 := hg.even
  rw [hp, hq] at b1 b2
  obtain ⟨Γ₀, p₀, q₀, g₀, s₀⟩ := UpperTheory.exists_geo_of_signature_rank_bounds D W.ψ T A A' WW X F₀ F₀' FW₀ hXi.rank Bs p q hB.2.1 hB.1.1 hB.2.2.1
    hXi.rigA hXi.rigA' hXi.rigW hXi.meas hXi.meas' nA nA' nW b4 (by omega) b2 hg.kappa
  have rd : ∀ s, (s = t ∨ s = μ₀) → GlobalTheory.StageGeo.Reads (fun t => Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (fun _ => G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (locPl G) Bs s (GlobalTheory.SqStep.chs G i j s) := by
    rintro s (rfl | rfl)
    · exact readings_of_split_units hL i j _ hB.1.2.1 hB.1.2.2.2 (q2 _)
    · exact readings_of_split_units hL i j _ hB.2.2.2.2.1.sub (base_split_prime_in_local_places hL hB.1) (q2 _)
  obtain ⟨κ, k, hκ⟩ := common_factor_of_pair_relation (t := t) (u := μ₀) (fun s => (GlobalTheory.SqStep.chs G i j s).ν) lam hF.1
    (fun s c => ∃ om om' Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf c) (by
    rintro s₁ s₂ c₁ c₂ h₁ h₂ ⟨o₁, o₁', R₁, m₁, k₁⟩ ⟨o₂, o₂', R₂, m₂, k₂⟩
    obtain ⟨e, cA, cB, hv⟩ := (hs s₁ h₁).2.2.2.2 o₁ o₁' m₁.triple
    obtain ⟨G₂, S₂⟩ := stage_regular_geometry hO hg g₀ (p₀.trans hp.symm) (q₀.trans hq.symm) s₀ hv.JW hv.JW₁ hv.measW hv.domW hv.measW₁ hv.domW₁
    have t₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs (GlobalTheory.ThK.reG Γ Γ₀.V Γ₀.V' Γ₀.W) (GlobalTheory.SqStep.chs G i j s₁) o₁ o₁' :=
      ⟨m₁.triple.base, G₂, m₁.triple.chars, m₁.triple.weil, m₁.triple.weil'⟩
    have t₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs (GlobalTheory.ThK.reG Γ Γ₀.V Γ₀.V' Γ₀.W) (GlobalTheory.SqStep.chs G i j s₂) o₂ o₂' :=
      ⟨m₂.triple.base, G₂, m₂.triple.chars, m₂.triple.weil, m₂.triple.weil'⟩
    obtain ⟨R', Sa, Sb, da, db, n₁, n₂, l₁, l₂, hdb⟩ := _root_.exists_pivot_pair hP hK hM t₁ t₂
    have E1 := _root_.GlobalTheory.StageGeo.geometric_stage_constant_ratio hP hK hM hXi S₂ hd hF (rd s₁ h₁) (rd s₂ h₂) n₁ n₂ l₁ l₂
    obtain ⟨k, E2⟩ := _root_.GlobalTheory.ReBase.rebase_ratio_real_part hP hK m₁ m₂ n₁ n₂ k₁ k₂ l₁ l₂
    refine ⟨k⁻¹, ?_⟩
    have z₁ : (((GlobalTheory.SqStep.chs G i j s₁).ν k : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have z₂ : (((GlobalTheory.SqStep.chs G i j s₂).ν k : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    rw [Circle.coe_div] at E2
    rw [map_inv, map_inv, Circle.coe_inv, Circle.coe_inv]
    generalize (((GlobalTheory.SqStep.chs G i j s₁).ν k : Circle) : ℂ) = n₁ at z₁ E2 ⊢
    generalize (((GlobalTheory.SqStep.chs G i j s₂).ν k : Circle) : ℂ) = n₂ at z₂ E2 ⊢
    have E3 : da * c₂ * n₂ = n₁ * (db * c₁) := by rw [E2]; field_simp
    have E4 : n₁ * c₁ * lam s₂ = n₂ * c₂ * lam s₁ :=
      mul_left_cancel₀ hdb (by linear_combination (-lam s₂) * E3 + c₂ * n₂ * E1)
    calc n₂⁻¹ * c₁ * lam s₂ = n₁⁻¹ * n₂⁻¹ * (n₁ * c₁ * lam s₂) := by field_simp
      _ = n₁⁻¹ * c₂ * lam s₁ := by rw [E4]; field_simp)
  obtain ⟨-, Pm, pp, pp', J, hsurj, -, -, hI, hI', -⟩ := hF
  obtain ⟨P, eP⟩ := hsurj (κ • pp' P')
  refine ⟨P, k, fun s hs' om om' Rf c m kc h => ?_⟩
  rw [hI, hI' s P' (hint s hs'), eP, map_smul, hκ s c hs' ⟨om, om', Rf, m, kc⟩]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomThetaNormEqProdLocalFactors
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.BottomFactor
open GlobalTheory.SquareComm in
theorem bottom_theta_norm_factorization : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe →
    GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X →
      ∃ (Pi : ModuleCat.{0} ℂ) (p : PolF D WW.rank A.rank →ₗ[ℂ] Pi) (p' : PolF D WW.rank A'.rank →ₗ[ℂ] Pi)
        (J : T → (Pi →ₗ[ℂ] (GA D WW → ℂ))), Function.Surjective p ∧ (∃ P', p' P' ≠ 0) ∧
        (∀ t, J t = 0 ∨ Function.Injective (J t)) ∧ (∀ t, ∃ lam : ℂ, ∀ P, X.I W.ψ W.θ t P = lam • J t (p P)) ∧
        ∀ t P', X.I' W.ψ W.θ t P' = J t (p' P') := by
  intro hH hP hK hM _
  have hLM := _root_.GlobalTheory.T.twisted_local_factors_match hH hP hK hM
  have hTA := _root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hK hM
  obtain ⟨CF1, H1⟩ := _root_.GlobalTheory.BotDict.bottom_dictionary
  obtain ⟨CF2, H2⟩ := _root_.GlobalTheory.T.theta_bottom_finite_place_matching hH hP hK hM
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, G1⟩ := H1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, G2⟩ := H2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hμ G W i j A A' WW X hX => ?_⟩
  obtain ⟨FA, FA', FW, a, b, hdA, hdef, hdW, hD⟩ :=
    G1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX
  have hF := G2 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX
  obtain ⟨Pr, q, q', hq, hq', hLMt⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW a b
  have eI : ∀ t P, thetaInt (X.ω t) X.m X.fd (fockF W.ψ W.θ true FA FW (X.f t) P) = X.I W.ψ W.θ t P := fun t P => by
    funext h; simp only [thetaInt, Tri.I, (hD t).2.2.2.2.1]
  have eI' : ∀ t P, thetaInt (X.ω' t) X.m' X.fd' (fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.I' W.ψ W.θ t P := fun t P => by
    funext h; simp only [thetaInt, Tri.I', (hD t).2.2.2.2.2]
  have iI' : ∀ t P h, IntegrableOn (fun g => thetaKO (X.ω' t) g h (fockF W.ψ W.θ false FA' FW (X.f' t) P)) X.fd' X.m' :=
    fun t P h => by simp only [(hD t).2.2.2.2.2]; exact (hX.integrable t).2 P h
  have key : ∀ t, (∀ P', q' P' = 0 → X.I' W.ψ W.θ t P' = 0) ∧
      ((∀ P', X.I' W.ψ W.θ t P' = 0) ∨ ∀ P', X.I' W.ψ W.θ t P' = 0 → q' P' = 0) ∧
      (∃ lam : ℂ, ∀ P P', q P = q' P' → X.I W.ψ W.θ t P = lam • X.I' W.ψ W.θ t P') ∧ Nontrivial Pr := by
    intro t
    obtain ⟨hTr, hInf, hf, hf', -, -⟩ := hD t
    obtain ⟨hex, hfac⟩ := hLMt _ _ hTr hInf
    obtain ⟨Pm, rf, rl, p, p', hm⟩ := _root_.GlobalTheory.T.triple_weil_transfer_matching hH hP hK hM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex (X.ω t) (X.ω' t)
      (hX.is.weil t) (hX.is.weil' t)
    obtain ⟨Pf, r, r', e, -, -, hr, hr'⟩ := hfac _ _ _ _ _ _ _ hm
    obtain ⟨c, hc0, hc⟩ := hTA D W.ψ W.θ W.θ_is A A' WW FA FA' FW _ _ hTr X.m X.fd X.m' X.fd' hX.is.meas hX.is.meas'
      (X.ω t) (X.ω' t) Pm rf rl p p' hm
    have hrel := _root_.GlobalTheory.T.theta_integral_vanishes_on_finite_relations hP D W.ψ W.θ W.ψ_std W.θ_is A' WW FA' FW _ _ (X.ω' t) (hX.is.weil' t) hdef X.m' X.fd' hX.is.meas'
    have kerp' := finRel_le_ker p' hm.mapB.invf
    have memF : ∀ P', fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ algF W.ψ W.θ false FA' FW :=
      fun P' => Submodule.subset_span ⟨_, P', hf', rfl⟩
    have same : ∀ Ψ ∈ algF W.ψ W.θ false FA' FW, (∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m') →
        ∀ Φ₀, Ψ - Φ₀ ∈ finRel (X.ω' t) (algF W.ψ W.θ false FA' FW) → ModInt W.θ (X.ω' t) X.m' X.fd' Φ₀ →
        thetaInt (X.ω' t) X.m' X.fd' Ψ = thetaInt (X.ω' t) X.m' X.fd' Φ₀ := by
      intro Ψ _ hΨ Φ₀ hd hmod
      obtain ⟨N, K, hmod⟩ := hmod
      funext h
      have h0 := congrFun (hrel _ hd) h
      simp only [thetaInt, thetaKO_sub] at h0 ⊢
      rw [integral_sub (hΨ h) (hmod h).1] at h0
      exact sub_eq_zero.1 h0
    have kill : ∀ Ψ ∈ algF W.ψ W.θ false FA' FW, (∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m') →
        p' Ψ = 0 → thetaInt (X.ω' t) X.m' X.fd' Ψ = 0 := by
      intro Ψ hΨ hi hp
      obtain ⟨Φ₀, hΦ₀, hd, hmod, hI⟩ := hc Ψ hΨ
      have hp0 : p' Φ₀ = 0 := by
        have := kerp' hd
        rw [LinearMap.mem_ker, map_sub, hp, zero_sub, neg_eq_zero] at this
        exact this
      have h1 := hI 0 (zero_mem _) (by rw [map_zero, hp0])
      have h2 : thetaInt (X.ω t) X.m X.fd 0 = 0 := by funext h; simp [thetaInt, thetaKO_zero]
      rw [h2] at h1
      rw [same Ψ hΨ hi Φ₀ hd hmod]
      exact ((smul_eq_zero.1 h1.symm).resolve_left hc0)
    have hp'F : ∀ P', p' (fockF W.ψ W.θ false FA' FW (X.f' t) P') = e (q' P' ⊗ₜ r' (X.f' t)) := hr' _ hf'
    refine ⟨fun P' h0 => ?_, ?_, ?_, ?_⟩
    · rw [← eI']
      exact kill _ (memF P') (iI' t P') (by rw [hp'F, h0, TensorProduct.zero_tmul, map_zero])
    · by_cases hall : ∀ P', X.I' W.ψ W.θ t P' = 0
      · exact Or.inl hall
      refine Or.inr fun P' h0 => ?_
      by_contra hq0
      refine hall fun P'' => ?_
      rw [← eI']
      by_cases hy : r' (X.f' t) = 0
      · exact kill _ (memF P'') (iI' t P'') (by rw [hp'F, hy, TensorProduct.tmul_zero, map_zero])
      · have hne : p' (fockF W.ψ W.θ false FA' FW (X.f' t) P') ≠ 0 := by
          rw [hp'F]; exact e.map_ne_zero_iff.2 (tmul_ne_zero' hq0 hy)
        exact _root_.GlobalTheory.T.theta_lift_vanishes_of_irreducible_defect hH hP hK hM hTA D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hdA hdef hdW X.m X.fd X.m' X.fd' hX.is.meas hX.is.meas'
          (X.ω t) (X.ω' t) Pm rf rl p p' hm _ (memF P') hne (by rw [eI']; exact h0) _ (memF P'')
    · obtain ⟨κ, hκ⟩ := hF FA FA' FW t hf hf' Pm rf rl p p' hm Pr Pf q q' r r' e hq hq' hr hr'
      refine ⟨c * κ, fun P P' hPP => ?_⟩
      set Ψ := κ • fockF W.ψ W.θ false FA' FW (X.f' t) P' with hΨdef
      have hΨ : Ψ ∈ algF W.ψ W.θ false FA' FW := Submodule.smul_mem _ _ (memF P')
      have hΨi : ∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m' := fun h => by
        simp only [hΨdef, thetaKO_smul]; exact (iI' t P' h).const_mul κ
      obtain ⟨Φ₀, -, hd, hmod, hI⟩ := hc Ψ hΨ
      have hpp : p (fockF W.ψ W.θ true FA FW (X.f t) P) = p' Φ₀ := by
        have h1 : p' Φ₀ = p' Ψ := by
          have := kerp' hd
          rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
          exact this.symm
        rw [h1, hΨdef, map_smul, hp'F, hr _ hf, hκ, hPP, TensorProduct.tmul_smul, map_smul]
      have h2 := hI _ (Submodule.subset_span ⟨_, P, hf, rfl⟩) hpp
      rw [eI, ← same Ψ hΨ hΨi Φ₀ hd hmod] at h2
      rw [h2, ← eI', mul_smul]
      congr 1
      funext h
      simp [hΨdef, thetaInt, thetaKO_smul, integral_const_mul]
    · obtain ⟨hnt, -⟩ := hm.irred
      by_contra hP0
      rw [not_nontrivial_iff_subsingleton] at hP0
      have hz : ∀ z : Pr ⊗[ℂ] Pf, z = 0 := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
        | add x y hx hy => rw [hx, hy, add_zero]
      obtain ⟨u, v, huv⟩ := hnt.exists_pair_ne
      exact huv (by rw [← e.apply_symm_apply u, ← e.apply_symm_apply v, hz (e.symm u), hz (e.symm v)])
  choose hker hirr hlam hnt using key
  let Il : T → PolF D WW.rank A'.rank →ₗ[ℂ] (GA D WW → ℂ) := fun t =>
    { toFun := fun P' => X.I' W.ψ W.θ t P'
      map_add' := fun P Q => by
        show X.I' W.ψ W.θ t (P + Q) = X.I' W.ψ W.θ t P + X.I' W.ψ W.θ t Q
        rw [← eI', ← eI', ← eI', map_add (f := _)]; funext h
        simp only [thetaInt, thetaKO_add, Pi.add_apply]
        exact integral_add (iI' t P h) (iI' t Q h)
      map_smul' := fun c P => by
        show X.I' W.ψ W.θ t (c • P) = c • X.I' W.ψ W.θ t P
        rw [← eI', ← eI', map_smul]; funext h
        simp [thetaInt, thetaKO_smul, integral_const_mul] }
  have hK : ∀ t, LinearMap.ker q' ≤ LinearMap.ker (Il t) := fun t P' h0 => hker t P' h0
  let J : T → (Pr →ₗ[ℂ] (GA D WW → ℂ)) := fun t =>
    ((LinearMap.ker q').liftQ (Il t) (hK t)) ∘ₗ (q'.quotKerEquivOfSurjective hq').symm.toLinearMap
  have hJ : ∀ t P', J t (q' P') = X.I' W.ψ W.θ t P' := fun t P' => by
    have : (q'.quotKerEquivOfSurjective hq').symm (q' P') = Submodule.Quotient.mk P' := by
      rw [LinearEquiv.symm_apply_eq]; exact (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _).symm
    simp only [J, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]; rfl
  haveI := hnt μ₀
  obtain ⟨x, hx⟩ := exists_ne (0 : Pr)
  obtain ⟨P0, rfl⟩ := hq' x
  refine ⟨Pr, q, q', J, hq, ⟨P0, hx⟩, fun t => ?_, fun t => ?_, fun t P' => (hJ t P').symm⟩
  · rcases hirr t with h | h
    · left; refine LinearMap.ext fun x => ?_; obtain ⟨P', rfl⟩ := hq' x; rw [hJ, h P']; rfl
    · right; rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']; intro x hx0; obtain ⟨P', rfl⟩ := hq' x
      rw [hJ] at hx0; exact h P' hx0
  · obtain ⟨lam, hl⟩ := hlam t
    refine ⟨lam, fun P => ?_⟩
    obtain ⟨P', hP'⟩ := hq' (q P)
    rw [← hP', hJ]; exact hl P P' hP'.symm
end GlobalTheory.BottomFactor
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_theta_norm_eq_prod_local_factors : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∃ (Pi : ModuleCat.{0} ℂ) (p : PolF D WW.rank A.rank →ₗ[ℂ] Pi) (p' : PolF D WW.rank A'.rank →ₗ[ℂ] Pi) (J : T → (Pi →ₗ[ℂ] (GA D WW → ℂ))), Function.Surjective p ∧ (∃ P', p' P' ≠ 0) ∧ (∀ t, J t = 0 ∨ Function.Injective (J t)) ∧ (∀ t, ∃ lam : ℂ, ∀ P, X.I W.ψ W.θ t P = lam • J t (p P)) ∧ ∀ t P', X.I' W.ψ W.θ t P' = J t (p' P') := by
  first | exact @_root_.GlobalTheory.BottomFactor.bottom_theta_norm_factorization | exact _root_.GlobalTheory.BottomFactor.bottom_theta_norm_factorization | (intros; apply _root_.GlobalTheory.BottomFactor.bottom_theta_norm_factorization <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SmallStageThetaIntegralLargeRankCase
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.StageSmallBig
theorem smallStage_thetaIntegral_of_large_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      1 ≤ q → ∃ P' : PolF D WW.rank A'.rank, (∀ t h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  intro hP hK hL
  have hH := hP.howeDualityReal
  have hLM := _root_.GlobalTheory.T.twisted_local_factors_match hH hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and GlobalTheory.T.towerStage_seesawDictionary_framesSignatures (_root_.GlobalTheory.T.theta_stage_nonzero_at_finite_places hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hLc G W S hW hN i j p q0 A A' WW X hX _ => ?_⟩
  obtain ⟨hd, h3⟩ := h C hC D large₂ a b r T Lc μ hLc G
  obtain ⟨FA, FA', FW, ea, eb, -, -, -, hD⟩ := hd W i j p q0 A A' WW X hX
  have hIs := hX.2.2.2.2.2.2.2
  obtain ⟨Pr, q, q', hq, hq', hLMt⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW ea eb
  obtain ⟨P0, hP0⟩ := _root_.GlobalTheory.T.fock_model_admissible_polynomial_exists hP hK hL D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW ea eb
  have key : ∀ t, (∀ h, IntegrableOn (X.ker' W.ψ W.θ t P0 h) X.fd' X.m') ∧ X.I' W.ψ W.θ t P0 ≠ 0 := by
    intro t
    obtain ⟨hTr, hInf, hf, hf', -, hk'⟩ := hD t
    obtain ⟨hex, hfac⟩ := hLMt _ _ hTr hInf
    obtain ⟨Pm, rf, rl, pm, pm', hm⟩ := _root_.GlobalTheory.T.triple_weil_transfer_matching hH hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex
      (X.ω t) (X.ω' t) (hIs.weil t) (hIs.weil' t)
    obtain ⟨Pf, rr, rr', e, -, -, hr, hr'⟩ := hfac _ _ _ _ _ _ _ hm
    have hy := h3 W i j p q0 A A' WW X hX FA FA' FW t hf hf' Pm rf rl pm pm' hm Pr Pf q q' rr rr' e hq hq' hr hr'
    haveI : Nontrivial Pm := hm.irred.1
    haveI : Nontrivial Pr := nontrivial_left e
    obtain ⟨x, hx⟩ := exists_ne (0 : Pr)
    obtain ⟨P1, rfl⟩ := hq' x
    obtain ⟨hint, hker⟩ := hP0 _ _ hTr hInf _ _ _ _ _ _ _ hm _ hf'
    have hint' := hint X.m' X.fd' hIs.meas'
    have hne : pm' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P0) ≠ 0 := fun h0 => by
      have h1 := hker h0 P1
      rw [hr' _ hf'] at h1
      exact e.map_ne_zero_iff.2 (tmul_ne_zero hx hy) h1
    have eI' : GlobalTheory.SquareComm.thetaInt (X.ω' t) X.m' X.fd' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P0) =
        X.I' W.ψ W.θ t P0 := by
      funext h; simp only [GlobalTheory.SquareComm.thetaInt, Tri.I', hk']
    refine ⟨fun h => ?_, ?_⟩
    · have h1 := hint' h
      simp only [hk'] at h1
      exact h1
    · rw [← eI']
      exact _root_.GlobalTheory.ConvThetaNe.convergent_theta_integral_ne_zero hP hK hL D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW _ _ hTr X.m' X.fd' hIs.meas'
        _ _ _ _ _ _ _ hm _ (Submodule.subset_span ⟨_, P0, hf', rfl⟩) hint' hne
  exact ⟨P0, fun t => (key t).1, fun t => (key t).2⟩
end GlobalTheory.StageSmallBig
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallStage_thetaIntegral_large_rank_case : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      1 ≤ q → ∃ P' : PolF D WW.rank A'.rank, (∀ t h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  first | exact @_root_.GlobalTheory.StageSmallBig.smallStage_thetaIntegral_of_large_rank | exact _root_.GlobalTheory.StageSmallBig.smallStage_thetaIntegral_of_large_rank | (intros; apply _root_.GlobalTheory.StageSmallBig.smallStage_thetaIntegral_of_large_rank <;> assumption)
end
end

