module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1993
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleFirstFactor
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IrrCoinvV

theorem irrV : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Fv F v) → ℂ), augAt om v ≤ N → N ≤ SB _ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ ∈ N) →
      N = augAt om v ∨ N = SB _ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hnr N hAN hNS hstab
  obtain ⟨ν₀, β₀, ι, ⟨t, ht⟩, s1, u1, s2, u2, hbij, hg1, hg2, hh⟩ := _root_.GlobalTheory.WeilLinA.localOps_eq_omA hP F E σ B a a' G X om om' hT v hv
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have hν : ν₀ (unifAt v) ≠ 1 := by
    have h1 := hnr t 1 one_ne_zero
    rw [zpow_one] at h1
    rcases ht with rfl | rfl
    · exact h1
    · intro h; apply h1; simpa using congrArg (·⁻¹) h
  set augL : Submodule ℂ (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ) := Submodule.span ℂ
    {z | ∃ (g : GL (Fin a) (Fv F v)) (Ψ : Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ),
      Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) ∧ z = GlobalTheory.SplitFlip.omA ν₀ β₀ g 1 Ψ - Ψ} with haugL
  have augS : augAt om v ≤ SB _ :=
    Submodule.span_le.mpr fun _ ⟨_, _, _, hφ, _, hφ₁, _, e⟩ => e ▸ sub_mem hφ₁ hφ
  have c1 : augAt om v ≤ augL.comap ι := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩
    obtain ⟨g', hg'⟩ := hg1 g hg
    show ι (φ₁ - φ) ∈ augL
    rw [map_sub, hg' φ hφ φ₁ hφ₁ hA]
    exact Submodule.subset_span ⟨g', ι φ, hbij.mapsTo hφ, rfl⟩
  have c2 : augL ≤ (augAt om v).map ι := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g', Ψ, hΨ, rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΨ
    obtain ⟨g, hg, hgg⟩ := hg2 g'
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hgg φ hφ
    refine ⟨φ₁ - φ, Submodule.subset_span ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩, ?_⟩
    rw [map_sub, he]
  have c3 : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ ∈ augL → φ ∈ augAt om v := by
    intro φ hφ h
    obtain ⟨ψ, hψ, he⟩ := c2 h
    rwa [← hbij.injOn (augS hψ) hφ he]
  set N' := N.map ι with hN'
  have n1 : augL ≤ N' := c2.trans (Submodule.map_mono hAN)
  have n2 : N' ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) := by
    rintro _ ⟨φ, hφ, rfl⟩; exact hbij.mapsTo (hNS hφ)
  have n3 : ∀ (h' : GL (Fin (a + a')) (Fv F v)), ∀ Ψ ∈ N', GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h' Ψ ∈ N' := by
    rintro h' _ ⟨φ, hφ, rfl⟩
    obtain ⟨h, hhW, hk⟩ := hh h'
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hk φ (hNS hφ)
    exact ⟨φ₁, hstab h hhW φ hφ φ₁ hφ₁ hA, he⟩
  have hle : a ≤ a + a' := Nat.le_add_right a a'
  rcases _root_.GlobalTheory.RankFibre.coinv_or_fullRank_le hP.bernsteinUnitaryProductIrreducible (Fv F v) a (a + a') hle ν₀ β₀ s1 u1 s2 u2 N' n1 n2 n3 with hA | hB
  · left
    refine le_antisymm (fun φ hφ => ?_) hAN
    have hφS := hNS hφ
    obtain ⟨Ψ₀, hΨ₀, hr, hd⟩ := _root_.GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan (Fv F v) a (a + a') hle ν₀ β₀ s1 u1 (unifAt v) hϖ hν (ι φ) (hbij.mapsTo hφS)
    have h0 : Ψ₀ ∈ N' := by
      have := N'.sub_mem (Submodule.mem_map_of_mem hφ) (n1 hd)
      rwa [sub_sub_cancel] at this
    have h1 := hA Ψ₀ h0 hr
    refine c3 φ hφS ?_
    have := augL.add_mem hd h1
    rwa [sub_add_cancel] at this
  · right
    refine le_antisymm hNS (fun φ hφS => ?_)
    obtain ⟨Ψ₀, hΨ₀, hr, hd⟩ := _root_.GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan (Fv F v) a (a + a') hle ν₀ β₀ s1 u1 (unifAt v) hϖ hν (ι φ) (hbij.mapsTo hφS)
    have h0 : ι φ ∈ N' := by
      have := N'.add_mem (n1 hd) (hB Ψ₀ hΨ₀ hr)
      rwa [sub_add_cancel] at this
    obtain ⟨n, hn, he⟩ := h0
    rwa [← hbij.injOn (hNS hn) hφS he]

end GlobalTheory.IrrCoinvV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UTau0

section Bal

variable {R : Type} [CommRing R] {B : Over (Sp R)} [GrpObj B] [IsCommMonObj B] (M : RigLB B) (cub : CubicalStr B M)
  {O : Type} [CommRing O] [StarRing O] (act : RingAct B O) {X : Type} [AddCommGroup X] [Module O X]
  (c : X → (𝟙_ (Over (Sp R)) ⟶ B))

def BalTau (τ : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε)) : Prop :=
  (∀ y z, (τ y z).IsGen) ∧
  (∀ y y' z p J, Good M.L p J →
    val (τ (y + y') z) (𝟙 _) p J * cubV cub p J (c y) (c y') (c z) =
      val (τ y z) (𝟙 _) p J * val (τ y' z) (𝟙 _) p J) ∧
  (∀ y z z' p J, Good M.L p J →
    val (τ y (z + z')) (𝟙 _) p J * cubV cub p J (c z) (c z') (c y) =
      val (τ y z) (𝟙 _) p J * val (τ y z') (𝟙 _) p J) ∧
  (∀ (a : O) (u : LB.Gen (LB.LinComb M.L (rosatiφ B (act.act a) (act.act (star a))) rosatiε)), u.IsGen →
    LB.Gen.Corr M.L _ _ _ _ (LB.pullGen M.L _ _ u (zero2 B)) (LB.oneGen M.L) →
    ∀ y z p J, Good M.L p J →
      val (τ (a • y) z) (𝟙 _) p J * val u (lift (c y) (c z)).left p J = val (τ y (star a • z)) (𝟙 _) p J)

end Bal

section Psi

variable {R : Type} [CommRing R] [IsDomain R]

abbrev w0φ (D₀ : DegPre R) (f : D₀.P.A ⟶ D₀.P.A) : Fin 4 → (D₀.P.A.left ⟶ D₀.P.A.left) :=
  ![(padd D₀.P.A (𝟙 _) f).left, 𝟙 D₀.P.A.left, f.left, (toUnit D₀.P.A ≫ η[D₀.P.A]).left]

abbrev w0ε : Fin 4 → ℤ := ![1, -2, -1, 2]

def rigV (D₀ : DegPre R) (p : Sp R) (J : (Sp R ⟶ D₀.P.A.left) → D₀.P.L.ι) :=
  val (L := D₀.P.L) (φ := fun _ : PUnit => eSec D₀.P.A) (ε := fun _ => 1) D₀.rig (𝟙 _) p J

def tauV (D₀ : DegPre R)
    (ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)))
    (p : Sp R) (J : (Sp R ⟶ D₀.P.A.left) → D₀.P.L.ι) (y z : D₀.X) :=
  val (ψ (y + z)) (𝟙 _) p J * (val (ψ y) (𝟙 _) p J)⁻¹ * (val (ψ z) (𝟙 _) p J)⁻¹ * (rigV D₀ p J)⁻¹

def RLaws (D₀ : DegPre R) {O : Type} [CommRing O] [StarRing O] [Module O D₀.X] (onB : D₀.P.OAct O) (w0 : O)
    (uw : LB.Gen (LB.LinComb D₀.P.L (w0φ D₀ (onB.act w0)) w0ε))
    (ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1))) : Prop :=
  (∀ y, (ψ y).IsGen) ∧
  (∀ y y' z p J, Good D₀.P.L p J →
    tauV D₀ ψ p J (y + y') z * cubV D₀.cub p J (D₀.c y) (D₀.c y') (D₀.c z) = tauV D₀ ψ p J y z * tauV D₀ ψ p J y' z) ∧
  (∀ y p J, Good D₀.P.L p J → val (ψ (-y)) (𝟙 _) p J * val D₀.sym (D₀.c y).left p J = val (ψ y) (𝟙 _) p J) ∧
  (∀ (a : O) (u : LB.Gen (LB.LinComb D₀.P.L (rosatiφ D₀.P.A (onB.act a) (onB.act (star a))) rosatiε)), u.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (zero2 D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ y z p J, Good D₀.P.L p J →
      tauV D₀ ψ p J (a • y) z * val u (lift (D₀.c y) (D₀.c z)).left p J = tauV D₀ ψ p J y (star a • z)) ∧
  (∀ y p J, Good D₀.P.L p J →
    tauV D₀ ψ p J y (w0 • y) * val uw (D₀.c y).left p J = val (ψ y) (𝟙 _) p J * rigV D₀ p J)

end Psi

end GlobalTheory.UTau0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedSymmetricPairMatrixHorizontalSingle
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogKSDiv.PairEntry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem mem_psiSet_iff (τ : E →+* ℂ) : τ ∈ psiSet H ↔ τ (H.rt : E) = H.rt0 := by
  simp [psiSet]

def pairToH : GlobalTheory.LogKSDiv.PairIx H Dw ≃ HIx Dw (psiSet H) where
  toFun P := ⟨⟨P.1.1, (mem_psiSet_iff _).2 P.1.2⟩, P.2.2, P.2.1⟩
  invFun k := ⟨⟨k.1.1, (mem_psiSet_iff _).1 k.1.2⟩, k.2.2, k.2.1⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem symPair_entry {R : Type} [CommRing R] {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (P : GlobalTheory.LogKSDiv.PairIx H Dw) (k : HIx Dw (psiSet H)) :
    GlobalTheory.LogKSDiv.symPair (R := R) e P (e ⟨k.1.1, k.2.2⟩) (e ⟨conjEmb k.1.1, k.2.1⟩) =
      if pairToH P = k then 1 else 0 := by
  obtain ⟨⟨τ, hτ⟩, i, k'⟩ := P
  obtain ⟨⟨σ, hσ⟩, a, b⟩ := k
  have hσ' : σ (H.rt : E) = H.rt0 := (mem_psiSet_iff _).1 hσ
  have h2 : ¬ (e ⟨σ, b⟩ = e ⟨(starRingEnd ℂ).comp τ, k'⟩ ∧ e ⟨conjEmb σ, a⟩ = e ⟨τ, i⟩) := by
    rintro ⟨h, -⟩
    have h5 : σ = (starRingEnd ℂ).comp τ := congrArg Sigma.fst (e.injective h)
    exact GlobalTheory.LogKSDiv.DetChange.conj_off H τ hτ (h5 ▸ hσ')
  simp only [GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
  rw [if_neg h2, add_zero]
  by_cases h : τ = σ
  · subst h
    have key : (e ⟨τ, b⟩ = e ⟨τ, i⟩ ∧ e ⟨conjEmb τ, a⟩ = e ⟨(starRingEnd ℂ).comp τ, k'⟩) ↔
        pairToH (Dw := Dw) ⟨⟨τ, hτ⟩, (i, k')⟩ = ⟨⟨τ, hσ⟩, (a, b)⟩ := by
      simp only [e.apply_eq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩
        have hb : b = i := eq_of_heq (Sigma.mk.inj_iff.1 h1).2
        have ha : a = k' := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
        subst hb ha
        rfl
      · intro h4
        have h5 := (Sigma.mk.inj_iff.1 h4).2
        simp only [heq_iff_eq, Prod.mk.injEq] at h5
        obtain ⟨rfl, rfl⟩ := h5
        exact ⟨rfl, rfl⟩
    exact if_congr key rfl rfl
  · have h3 : ¬ (e ⟨σ, b⟩ = e ⟨τ, i⟩ ∧ e ⟨conjEmb σ, a⟩ = e ⟨(starRingEnd ℂ).comp τ, k'⟩) := by
      rintro ⟨h4, -⟩
      exact h (congrArg Sigma.fst (e.injective h4)).symm
    rw [if_neg h3, if_neg]
    intro h4
    exact h (congrArg (fun x : HIx Dw (psiSet H) => x.1.1) h4)

end GlobalTheory.LogKSDiv.PairEntry

namespace GlobalTheory.LogKSDiv.PairEntry

theorem symPair_horizontal_single : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw), ∃ κ : Fin Dw.dim ≃ HIx Dw (psiSet H), ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (j : Fin Dw.dim) (k : HIx Dw (psiSet H)), f (GlobalTheory.LogKSDiv.symPair (R := R) e (ε j) (e ⟨k.1.1, k.2.2⟩) (e ⟨conjEmb k.1.1, k.2.1⟩)) = (Pi.single (κ j) (1 : S) : HIx Dw (psiSet H) → S) k := by
  intro E _ _ _ H Dw ε
  refine ⟨ε.trans pairToH, fun f n e j k => ?_⟩
  rw [symPair_entry, Pi.single_apply, Equiv.trans_apply]
  by_cases h : pairToH (ε j) = k
  · rw [if_pos h, if_pos h.symm, map_one]
  · rw [if_neg h, if_neg (Ne.symm h), map_zero]

end GlobalTheory.LogKSDiv.PairEntry
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcR
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

section Defs
variable {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left)

abbrev bc : Over (Sp V) := (Over.pullback (φ ≫ T.hom)).obj A

abbrev bcR : Over (Sp R) := Over.mk ((bc A φ).hom ≫ φ ≫ T.hom)

def pa : bcR A φ ⟶ A := Over.homMk (pullback.fst A.hom (φ ≫ T.hom)) (by
  show pullback.fst A.hom (φ ≫ T.hom) ≫ A.hom = pullback.snd A.hom (φ ≫ T.hom) ≫ φ ≫ T.hom
  exact pullback.condition)

def pt : bcR A φ ⟶ T := Over.homMk ((bc A φ).hom ≫ φ) (Category.assoc _ _ _)

def twist (N : LB (A ⊗ T).left) : LB (bcR A φ).left := N.pull (lift (pa A φ) (pt A φ)).left

abbrev ker {H : Over (Sp R)} (h : H ⟶ A ⊗ T) : Over (Sp V) := Over.mk (pullback.snd (h ≫ snd A T).left φ)

def kerι {H : Over (Sp R)} (h : H ⟶ A ⊗ T) : ker A φ h ⟶ bc A φ :=
  Over.homMk (pullback.lift (pullback.fst (h ≫ snd A T).left φ ≫ (h ≫ fst A T).left) (pullback.snd _ _) (by
    have w : (h ≫ fst A T).left ≫ A.hom = (h ≫ snd A T).left ≫ T.hom := by rw [Over.w, Over.w]
    rw [Category.assoc, w, pullback.condition_assoc])) (pullback.lift_snd _ _ _)

variable {A}

abbrev up (Y : Over (Sp V)) : Over (Sp R) := Over.mk (Y.hom ≫ φ ≫ T.hom)

def upa {Y : Over (Sp V)} (x : Y ⟶ bc A φ) : up φ Y ⟶ A :=
  Over.homMk (x.left ≫ pullback.fst A.hom (φ ≫ T.hom)) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ φ ≫ T.hom) (Over.w x))

def upt (Y : Over (Sp V)) : up φ Y ⟶ T := Over.homMk (Y.hom ≫ φ) (Category.assoc _ _ _)

end Defs
end GlobalTheory.TwistFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellPointEqOfBaseAndCellCoordinatesEqStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigCell_point_eq_of_base_and_cellCoordinates_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N) (S : Type) [CommRing S] (z₁ z₂ : Sp S ⟶ Y₀ TF.X Z) (h₁ : ⊤ ≤ z₁ ⁻¹ᵁ W) (h₂ : ⊤ ≤ z₂ ⁻¹ᵁ W), ⊤ ≤ z₁ ⁻¹ᵁ U₀ TF.X Z → ⊤ ≤ z₂ ⁻¹ᵁ U₀ TF.X Z → (∀ r, ev z₁ W h₁ (((toBase TF Z).appLE U.1 W h.2.1).hom r) = ev z₂ W h₂ (((toBase TF Z).appLE U.1 W h.2.1).hom r)) → (∀ i, ev z₁ W h₁ (cellCoord N i) = ev z₂ W h₂ (cellCoord N i)) → z₁ = z₂ := by
  first | exact @GlobalTheory.LogPole.eq_of_cellCoord_eq | exact GlobalTheory.LogPole.eq_of_cellCoord_eq | (intros; apply GlobalTheory.LogPole.eq_of_cellCoord_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiholomorphicLiftSystem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime]

theorem Datum.algebraMap_injective (D : Datum p) (hm : D.m = 1) :
    Function.Injective (algebraMap (𝓞 D.F) D.O) := by
  haveI := D.freeO
  haveI := D.finO
  haveI : Nontrivial D.O := by
    apply Module.nontrivial_of_finrank_pos (R := ℤ)
    rw [D.rankO, hm]; simpa using Module.finrank_pos (R := ℚ) (M := D.F)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have hF : (a : D.F) ≠ 0 := by exact_mod_cast ha0
  obtain ⟨y, hy0, hyint⟩ := IsAlgebraic.exists_integral_multiple
    (a.2.isAlgebraic.inv)
  set b : 𝓞 D.F := ⟨_, hyint⟩
  have hab : a * b = (y : 𝓞 D.F) := by
    apply RingOfIntegers.coe_injective
    simp only [map_mul, map_intCast]
    show (a : D.F) * ((y : ℤ) • (a : D.F)⁻¹) = _
    rw [zsmul_eq_mul]
    field_simp
  have h1 : algebraMap (𝓞 D.F) D.O (y : 𝓞 D.F) = 0 := by rw [← hab, map_mul, ha, zero_mul]
  rw [map_intCast] at h1
  have : (y : ℤ) • (1 : D.O) = 0 := by rw [zsmul_eq_mul, _root_.mul_one, h1]
  rcases smul_eq_zero.mp this with h | h
  · exact hy0 h
  · exact one_ne_zero h

theorem Datum.exists_zsmul_eq_algebraMap (D : Datum p) (hm : D.m = 1) (x : D.O) :
    ∃ e : ℤ, e ≠ 0 ∧ ∃ a : 𝓞 D.F, e • x = algebraMap (𝓞 D.F) D.O a := by
  haveI := D.freeO
  haveI := D.finO
  let f : 𝓞 D.F →ₗ[ℤ] D.O := (algebraMap (𝓞 D.F) D.O).toAddMonoidHom.toIntLinearMap
  have hf : Function.Injective f := D.algebraMap_injective hm
  let M := LinearMap.range f
  have h1 := rank_quotient_add_rank_of_isDomain M
  rw [rank_range_of_injective f hf, ← Module.finrank_eq_rank (R := ℤ) (M := 𝓞 D.F),
    ← Module.finrank_eq_rank (R := ℤ) (M := D.O), RingOfIntegers.rank, D.rankO, hm, one_pow,
    _root_.one_mul] at h1
  obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.mp (Module.rank_lt_aleph0 (R := ℤ) (M := D.O ⧸ M))
  rw [hk] at h1
  norm_cast at h1
  have h0 : Module.rank ℤ (D.O ⧸ M) = 0 := by rw [hk]; norm_cast; omega
  obtain ⟨e, he, hex⟩ := (rank_eq_zero_iff.mp h0) (Submodule.Quotient.mk x)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hex
  obtain ⟨a, ha⟩ := hex
  exact ⟨e, he, a, ha.symm⟩

theorem Datum.algebraMap_surjective_of_m_eq_one :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → Function.Surjective (algebraMap (𝓞 D.F) D.O) := by
  intro p _ D hm x
  haveI := D.freeO
  haveI := D.finO
  obtain ⟨e, he, a, ha⟩ := D.exists_zsmul_eq_algebraMap hm x
  haveI : Algebra.IsIntegral ℤ D.O := Algebra.IsIntegral.of_finite ℤ D.O
  obtain ⟨P, hPm, hP⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) x
  have h1 : Polynomial.aeval (algebraMap ℤ D.O e * x) (P.scaleRoots e) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero (by rwa [Polynomial.aeval_def])
  rw [← Algebra.smul_def, ha, Polynomial.aeval_algebraMap_apply] at h1
  have h2 : Polynomial.aeval a (P.scaleRoots e) = 0 :=
    D.algebraMap_injective hm (by rw [h1, map_zero])
  have he' : (e : D.F) ≠ 0 := by exact_mod_cast he
  have h4 : Polynomial.aeval (a : D.F) (P.scaleRoots e) = 0 := by
    have := congrArg (algebraMap (𝓞 D.F) D.F) h2
    rwa [← Polynomial.aeval_algebraMap_apply, map_zero] at this
  have h3 : Polynomial.eval₂ (algebraMap ℤ D.F) ((a : D.F) / e) P = 0 := by
    have := Polynomial.scaleRoots_eval₂_mul (p := P) (algebraMap ℤ D.F) ((a : D.F) / e) e
    rw [show algebraMap ℤ D.F e * ((a : D.F) / e) = (a : D.F) by
      rw [algebraMap_int_eq, eq_intCast]; field_simp] at this
    rw [← Polynomial.aeval_def, h4] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ (by simpa using he'))
  have hint : IsIntegral ℤ ((a : D.F) / e) := ⟨P, hPm, h3⟩
  obtain ⟨a', ha'⟩ : ∃ a' : 𝓞 D.F, (a' : D.F) = (a : D.F) / e := ⟨⟨_, hint⟩, rfl⟩
  refine ⟨a', ?_⟩
  have hae : a = e • a' := by
    apply RingOfIntegers.coe_injective
    rw [zsmul_eq_mul, map_mul, map_intCast]
    change (a : D.F) = (e : D.F) * (a' : D.F)
    rw [ha']
    field_simp
  apply smul_right_injective D.O he
  change e • algebraMap (𝓞 D.F) D.O a' = e • x
  rw [ha, ← map_zsmul, ← hae]

end GlobalTheory.UPel.HT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiOfSemilinearHom
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem kaehler_liftSemi_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (B B' : Type) [CommRing B] [CommRing B'] [Algebra R B] [Algebra R' B'] (α : B →+* B') (h : SemiHom (algebraMap R R') α) (f : B →ₛₗ[algebraMap R R'] B'), (∀ b, f b = α b) → Function.Bijective (liftSemi f) → Function.Bijective (liftSemi h.m1) := by
  intro R R' _ _ _ B B' _ _ _ _ α h f hf hb
  letI : Algebra B B' := α.toAlgebra
  letI : Algebra R B' := ((algebraMap R' B').comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun r ↦ (h.map_algebraMap r).symm
  let g : B →ₗ[R] B' := (IsScalarTower.toAlgHom R B B').toLinearMap
  have e1 : ⇑(g.liftBaseChange R') = ⇑(liftSemi f) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [g, hf]; rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  haveI : Algebra.IsPushout R R' B B' :=
    ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective (g.liftBaseChange R') (e1 ▸ hb)) fun n ↦ by simp [g]⟩
  have e2 : ∀ ω : Ω[B⁄R], h.m1 ω = KaehlerDifferential.map R R' B B' ω := by
    intro ω
    have hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      rw [SemiHom.m1_D, KaehlerDifferential.map_D]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | smul b x _ hx =>
      rw [SemiHom.oneFormMap_smul_semilinear, hx, LinearMap.map_smul_of_tower]
      exact algebraMap_smul B' b _
  have e3 : ⇑(liftSemi h.m1) = ⇑(KaehlerDifferential.tensorKaehlerEquivBase R R' B B') := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x ω => rw [liftSemi_tmul, KaehlerDifferential.tensorKaehlerEquivBase_tmul, e2]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [e3]
  exact (KaehlerDifferential.tensorKaehlerEquivBase R R' B B').bijective

end GlobalTheory
end

