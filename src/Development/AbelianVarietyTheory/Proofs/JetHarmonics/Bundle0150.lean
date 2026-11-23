module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionEq
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamObj
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.CMObjBundlePull
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyPowerDegree
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricLiftActsRootOfUnityOnExpansions
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Formalism.HermitianCurvature.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WaveGridLiftGridOfLayoutNormaliserBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConjCmHostRootNeSelf
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LeafCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7}

theorem conj_cmHostRoot_ne_self {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro h5
  obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h5
  have h6 := H.sqrt_neg_disc_sq
  rw [hx] at h6
  have h7 : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast h6
  have h8 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg x]

theorem tauEmb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauEmb_ne_conj (Q : Par D) (hp : Q.PinHost) (t t' : D.what₂.Tau) :
    DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 := hp.2.2.2 t
  rw [h] at h1
  have h2 : (starRingEnd ℂ) (DV.tauEmb D t' (Q.H.rt : D.host.E)) = Q.H.rt0 := h1
  rw [hp.2.2.2 t'] at h2
  exact conj_cmHostRoot_ne_self Q.H h2

theorem exists_tau (Q : Par D) (hp : Q.PinHost) (τ : D.host.E →+* ℂ) (hτ : InPsi Q.H τ) :
    ∃ t : D.what₂.Tau, τ = DV.tauEmb D t := by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 τ
  by_cases hgP : g ∈ D.R.Psi
  · obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 hgP
    exact ⟨t, hg.symm.trans ht⟩
  · exfalso
    have h2 : g * D.R.cc ∈ D.R.Psi := by
      by_contra h
      exact hgP ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g).2 h)
    obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2 h2
    have h3 : DV.tauEmb D t (Q.H.rt : D.host.E) = Q.H.rt0 := hp.2.2.2 t
    rw [← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg, RingHom.comp_apply] at h3
    have h4 : τ (D.host.conj (Q.H.rt : D.host.E)) = star (τ (Q.H.rt : D.host.E)) := Formalism.MainNotions.WeightFamilies.emb_conj D τ _
    have hτ' : τ (Q.H.rt : D.host.E) = Q.H.rt0 := hτ
    apply conj_cmHostRoot_ne_self Q.H
    calc star Q.H.rt0 = star (τ (Q.H.rt : D.host.E)) := by rw [hτ']
      _ = τ (D.host.conj (Q.H.rt : D.host.E)) := h4.symm
      _ = Q.H.rt0 := h3

theorem wtA_tau (Q : Par D) (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [tauEmb_ne_conj Q hp]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (tauEmb_inj h).symm
    simp [tauEmb_ne_conj Q hp, this]
  · simp

end GlobalTheory.LeafCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DimEqOfFiniteSurjective
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.LamCM Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTan
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull

namespace GlobalTheory.CMClaims

theorem laws : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
theorem secTwist : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
theorem homExt : CM.HomExtDvr := fun T K _ _ _ _ _ _ G G' _ _ hG hG' φ hφ =>
  GlobalTheory.existsUnique_hom_extension_semiAbelian T K G G' hG hG' φ hφ

section Vec

variable {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {G : Over (Sp R)} {G' : Over (Sp R')} [GrpObj G]
  [GrpObj G'] {φ : G'.left ⟶ G.left}

variable (h : IsGrpPullback G' G (spMap f) φ)

variable [IsCommMonObj G'] {n : ℕ} {v : Fin n → (epsR R' ⟶ G')} (hv : IsLieBasis v)

end Vec

section Pair

variable {K : Type} [Field K] [NumberField K]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E}

end Pair

section Isog

theorem card_torsion_eq {M N : Type} [CommGroup M] [CommGroup N] (F : M →* N) (hF : Function.Surjective F) (m : ℕ)
    (hm : ∀ x, F x = 1 → x ^ (m + 1) = 1) :
    Nat.card {x : M // x ^ (m + 2) = 1} = Nat.card {y : N // y ^ (m + 2) = 1} := by
  refine Nat.card_eq_of_bijective (fun x => ⟨F x.1, by rw [← map_pow, x.2, map_one]⟩) ⟨fun a b e => ?_, fun y => ?_⟩
  · have e₁ : F (a.1 / b.1) = 1 := by rw [map_div, div_eq_one]; exact congrArg Subtype.val e
    have e₂ : (a.1 / b.1) ^ (m + 2) = 1 := by rw [div_pow, a.2, b.2, div_one]
    rw [pow_succ, hm _ e₁, _root_.one_mul, div_eq_one] at e₂
    exact Subtype.ext e₂
  · obtain ⟨x, hx⟩ := hF y.1
    have e₁ : (x ^ (m + 2)) ^ (m + 1) = 1 := hm _ (by rw [map_pow, hx, y.2])
    refine ⟨⟨x ^ ((m + 1) * (m + 1)), ?_⟩, Subtype.ext ?_⟩
    · rw [← pow_mul, show (m + 1) * (m + 1) * (m + 2) = (m + 2) * (m + 1) * (m + 1) by ring, pow_mul, pow_mul, e₁, one_pow]
    · change F _ = y.1
      rw [map_pow, hx, show (m + 1) * (m + 1) = (m + 2) * m + 1 by ring, pow_succ, pow_mul, y.2, one_pow, _root_.one_mul]

variable {K : Type} [Field K] [NumberField K]

theorem onto_points {R k : Type} [CommRing R] [Field k] [IsAlgClosed k] {P Q : Over (Sp R)} (Φ : P ⟶ Q)
    [IsFinite Φ.left] [Surjective Φ.left] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ Q) : ∃ x : Over.mk t ⟶ P, y = x ≫ Φ := by
  obtain ⟨p, hp⟩ := GeomSurj.exists_lift_of_surjective Φ.left y.left
  refine ⟨Over.homMk p ?_, Over.OverMorphism.ext hp⟩
  rw [← Over.w Φ, ← Category.assoc, ← hp]
  exact Over.w y

end Isog

section Sum

variable {K : Type} [Field K] [NumberField K]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {c : Coeff l} {p q : ℕ}

end Sum

section Types

variable {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K} {φ : x.P.A.left ⟶ A.A.left}

variable {E : Type} [Field E] [NumberField E]

end Types

section Lines

variable {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K} {φ : x.P.A.left ⟶ A.A.left}

end Lines

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable [StarRing (𝓞 E)] {l : Level H} {c : Coeff l} {p q : ℕ}

def Readable (o : abelian₂.LamObj c p q) : Prop :=
  abelian₂.IsFibreOf o.AΨ o.xΨ (abelian₂.gmap o.K₁) o.φΨg ∧ abelian₂.IsFibreOf o.A' o.x' (abelian₂.gmap o.K₁) o.φ'g ∧
    (∀ i, IsMonHom (o.φΨ i)) ∧ (∀ i, IsMonHom (o.φ' i)) ∧
    (∀ i (a : 𝓞 E), o.oaΨ.act a ≫ o.φΨ i = o.φΨ i ≫ o.oa.act a) ∧
    ∀ i (a : 𝓞 E), o.oa'.act a ≫ o.φ' i = o.φ' i ≫ o.oa.act a

variable (hs : ∀ a : 𝓞 E, star a = H.bar a) (o : abelian₂.LamObj c p q) (h : Readable o)

end Main

end GlobalTheory.CMClaims
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DvdOfPullEqZero
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.BoxFrame

open GlobalTheory.IntegralBox

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem dvd_iff (D : DegPre V) {k : ℕ} {α : D.X} (a : V) (σ τ : SecMod D k α) :
    (∀ j, LB.Sec.f σ j = constFn D.P.A.hom _ a * LB.Sec.f τ j) ↔ σ = a • τ :=
  ⟨fun h => SecOps.sec_ext h, fun h j => congrArg (fun s : SecMod D k α => LB.Sec.f s j) h⟩

theorem dvd_of_pull_eq_zero (hT : TwistBaseChangeStatement) {ϖ : V} (hϖ : Irreducible ϖ) (D : DegPre V) {k : ℕ}
    (hk : 1 ≤ k) {α : D.X} (σ : SecMod D k α) (h : pullBC (residue V) D k α σ = 0) :
    ∃ τ : SecMod D k α, σ = ϖ • τ := by
  obtain ⟨b, hb, hb'⟩ := exists_basis (residue V) D hT hk α
  obtain ⟨c, rfl⟩ := hb σ
  have h0 := hb' (fun i => residue V (c i)) (by simpa only [map_sum, map_smulₛₗ] using h)
  have hd : ∀ i, ϖ ∣ c i := fun i => by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq, ← residue_eq_zero_iff]
    exact congrFun h0 i
  choose d hd using hd
  exact ⟨∑ i, d i • b i, by simp only [hd, Finset.smul_sum, smul_smul]⟩

theorem exists_pull_ne_zero (hT : TwistBaseChangeStatement) (D : DegPre V) (α : D.X) :
    ∃ σ : SecMod D 1 α, pullBC (residue V) D 1 α σ ≠ 0 := by
  classical
  obtain ⟨b, -, hb'⟩ := exists_basis (residue V) D hT le_rfl α
  let i₀ : Fin (1 ^ D.P.g) := ⟨0, by simp⟩
  refine ⟨b i₀, fun h => ?_⟩
  have h0 := hb' (Pi.single i₀ 1) (by
    rw [Finset.sum_eq_single i₀, h, smul_zero]
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h)
  simpa using congrFun h0 i₀

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀ (n : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre n) (F : Type) [Field F] [Algebra (FractionRing V) F] (θ : Fam D.toPre F 1) (Θ : Fam D'.toPre F 1), ThFrame D ϖ F θ → IsBoxFam pD F 1 Θ (fun _ => θ) → ThFrame D' ϖ F Θ := by
  intro V _ _ _ _ ϖ hϖ n D D' pD F _ _ θ Θ ⟨σ, σF, hs, he, hn⟩ hB
  have hT := GlobalTheory.twistBaseChange_and_valuation_statements.1
  have hex : ∀ α : D.toPre.X, ∃ s : SecMod D.toPre 1 α, pullBC (residue V) D.toPre 1 α s ≠ 0 ∧
      (α = 0 → GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε 1) (θ.s α)
        (D.toPre.famφB α) (DegPre.famε 1) s (DegPre.prB D.toPre F).left 1) := fun α => by
    by_cases hα : α = 0
    · subst hα
      refine ⟨σ, fun h => ?_, fun _ => ?_⟩
      · obtain ⟨τ, hτ⟩ := dvd_of_pull_eq_zero hT hϖ D.toPre le_rfl σ h
        exact hn ⟨τ, (dvd_iff D.toPre ϖ σ τ).2 hτ⟩
      · rw [show θ.s 0 = σF from SecOps.sec_ext he]
        exact hs
    · obtain ⟨s, hs⟩ := exists_pull_ne_zero hT D.toPre α
      exact ⟨s, hs, fun h => absurd h hα⟩
  choose f hf hf' using hex
  refine ⟨boxFamB pD 1 (fun _ α => f α) 0, Θ.s 0,
    UnitBallBox.box_secScal pD hB (isBoxFamB_boxFamB pD 1 _) 0
      (fun i => hf' _ (by rw [map_zero]; rfl)), fun _ => rfl, ?_⟩
  rintro ⟨τ, hτ⟩
  have h1 := (dvd_iff D'.toPre ϖ _ τ).1 hτ
  have h2 : residue V ϖ = 0 := (residue_eq_zero_iff _).2 (by
    rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ)
  have h3 : pullBC (residue V) D'.toPre 1 0 (boxFamB pD 1 (fun _ α => f α) 0) = 0 := by
    exact (congrArg _ h1).trans ((map_smulₛₗ (pullBC (residue V) D'.toPre 1 0) ϖ τ).trans (by rw [h2, zero_smul]))
  have h4 := box_indep (residue V) pD (m := 1) (fun α _ => f α) (fun α c hc => by
    rw [Fin.sum_univ_one, smul_eq_zero] at hc
    funext i
    rw [Subsingleton.elim i 0]
    exact hc.resolve_right (hf α)) 0 (fun _ => 1) (Finset.sum_eq_zero fun a _ => (congrArg _ h3).trans (smul_zero _))
  exact one_ne_zero (congrFun h4 fun _ => 0)

end GlobalTheory.BoxFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroEnergyLeOfEigenSum
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem levelZero_energy_le_of_eigen_sum :
    GlobalTheory.HCXi.BesselXiIntegrable → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (s : ℂ) (nn : ℝ → ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (s = 1 ∨ s = -1) → B.AB k r ≤ A → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) → (∀ y : ℝ, ∏ t, (|y + lam t| + (d : ℝ)) ≤ nn y) → ∀ w : List (Bool × ℝ), (C7.principalHermitianLattice D s w F).re ≤ (w.map fun l => nn l.2).prod * (B.beta D F F).re := by
  intro hXi k r Wp Wq _ _ _ _ _ _ D lam d A s nn F hs hA hex hnn w
  obtain ⟨N₀, Fi, ν, hν, hcl, hev, hF⟩ := hex
  obtain ⟨σ, hσs, hσ⟩ : ∃ σ : ℝ, s = (σ : ℂ) ∧ |σ| = 1 := by
    rcases hs with h | h
    · exact ⟨1, by simp [h], by simp⟩
    · exact ⟨-1, by simp [h], by simp⟩
  have h5 : ∀ i, B.InCC A 5 (Fi i) := fun i => (hcl i).2 5
  set e : Fin N₀ → ℝ → ℝ := fun i Y => ∏ t, (Y + lam t + (ν i t : ℝ)) with he
  set c : Fin N₀ → Bool × ℝ → ℝ := fun i a => σ * e i a.2 with hc
  have hF1 : ∀ g ∈ B.GV k r, F g = ∑ i ∈ Finset.univ, (1 : ℂ) • Fi i g := by
    intro g hg; simpa using hF g hg
  have hfold := GlobalTheory.foldr_capelli_sum_eigen k r Wp Wq N₀ Fi (fun i Y => ((e i Y : ℝ) : ℂ)) s F (fun i => (hcl i).1)
    (fun i Y g hg => hev i Y g hg) hF w
  have e1 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) Finset.univ Finset.univ _ (fun _ => 1) Fi _ F hA h5 hfold hF1
  have e2 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) Finset.univ Finset.univ (fun _ => 1) (fun _ => 1) Fi F F hA h5
    hF1 hF1
  have hcast : ∀ i, (w.map fun a => s * ((e i a.2 : ℝ) : ℂ)).prod = (((w.map (c i)).prod : ℝ) : ℂ) := by
    intro i
    have : ∀ v : List (Bool × ℝ),
        (v.map fun a => s * ((e i a.2 : ℝ) : ℂ)).prod = (((v.map (c i)).prod : ℝ) : ℂ) := by
      intro v
      induction v with
      | nil => simp
      | cons a v ih =>
        rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, hσs]
        simp only [hc, Complex.ofReal_mul]
    exact this w
  have key := gram_blockDiagonal_energy_bound (Fin N₀) (Bool × ℝ) (fun i j => B.beta D (Fi i) (Fi j)) c w
    (fun l => nn l.2) ?_ ?_ ?_
  · unfold C7.principalHermitianLattice
    rw [e1, e2]
    simp only [star_one, mul_one, one_mul, hcast]
    exact key
  · intro S
    have e3 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) S S (fun _ => 1) (fun _ => 1) Fi
      (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g) (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g) hA h5
      (fun _ _ => rfl) (fun _ _ => rfl)
    have e4 := GlobalTheory.BetaPos.beta_self_re_nonneg k r Wp Wq D (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g)
    rw [e3] at e4
    simpa only [star_one, mul_one, one_mul] using e4
  · intro i j a _ hne
    have hne' : e i a.2 ≠ e j a.2 := fun h => hne (by simp only [hc, h])
    have hsym := GlobalTheory.beta_capelli_symm_of_bessel hXi k r Wp Wq D a.2 A (Fi i) (Fi j) hA (hcl i) (hcl j)
    have h1 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) {i} {j}
      (fun _ => ((e i a.2 : ℝ) : ℂ)) (fun _ => 1) Fi (Q.CV k r (a.2 : ℂ) (Fi i)) (Fi j) hA h5
      (fun g hg => by rw [Finset.sum_singleton]; exact hev i a.2 g hg) (fun g _ => by simp)
    have h2 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) {i} {j}
      (fun _ => 1) (fun _ => ((e j a.2 : ℝ) : ℂ)) Fi (Fi i) (Q.CV k r (a.2 : ℂ) (Fi j)) hA h5
      (fun g _ => by simp) (fun g hg => by rw [Finset.sum_singleton]; exact hev j a.2 g hg)
    simp only [Finset.sum_singleton, star_one, mul_one, one_mul,
      Complex.star_def, Complex.conj_ofReal] at h1 h2
    rw [h1, h2] at hsym
    have hcc : ((e i a.2 : ℂ) - (e j a.2 : ℂ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne')
    have h0 : ((e i a.2 : ℂ) - (e j a.2 : ℂ)) * B.beta D (Fi i) (Fi j) = 0 := by
      rw [sub_mul, hsym, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left hcc
  · intro i a _
    refine le_trans ?_ (hnn a.2)
    simp only [hc, he, abs_mul, hσ, one_mul, Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun t _ => (abs_add_le _ _).trans ?_)
    have : |(ν i t : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hν i t
    linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricLiftActsRootOfUnityOnExpansionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_lift_acts_root_of_unity_on_expansions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∀ (q : ℕ), 1 ≤ q → ∀ (σ σ' : P.U.toUnifPre.SecGF F q) (hh hh' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))) (s t₀ t : Fam P.D.toPre F q) (x : TFK (R := T.V) F ⟶ P.A.A) (b : ptO Xo xF ⟶ Xo.univ.t.G) (p : QkPt P.D.toPre F q) (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε q))) (ζ : F), SecTieF I P F xF q σ hh → SecTieF I P F xF q σ' hh' → P.U.toUnifPre.ExpandsG F q σ s → IsSymAct Xo.univ.t.G Xo.univ.t.PP q b hh hh' → PtTieF I P F xF x b → P.ToA F q p x → w.IsGen → FinOrd P.D F q p w ζ → PhiRel P.D.toPre F q p w s t₀ → Fam.IsSmul P.D.toPre F ζ t₀ t → ∃ (u : F) (t' : Fam P.D.toPre F q), (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ Fam.IsSmul P.D.toPre F u t t' ∧ P.U.toUnifPre.ExpandsG F q σ' t' := by
  first | exact @GlobalTheory.SymActExpansion.exists_expandsG_of_isSymAct | exact GlobalTheory.SymActExpansion.exists_expandsG_of_isSymAct | (intros; apply GlobalTheory.SymActExpansion.exists_expandsG_of_isSymAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityCutoffEventuallyEqSmoothCoefficient
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

theorem Ew_cutF_eventually_eq : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → KB.CutWord P p.l0 w → ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c) = TBB.Ew p (fun _ => 1) f (P.r + 1) w (TBB.bigPt P.r c) := by
  intro Wp Wq _ _ _ _ _ _ P p Cb f χ w hΘ hχ hf hw
  obtain ⟨δ, hδ, hδχ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x, x < δ → χ x = 0 := by
    have h := hχ
    unfold C6.IsCut0 at h
    tauto
  refine Filter.Eventually.of_forall fun c => ?_
  simp only [Ew_eq_norm_tv_sq]
  by_cases hG : 0 < TBB.Gp p (TBB.bigPt P.r c)
  · filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
    rw [(GlobalTheory.T.topVector_cutoff_eq_and_vanish Wp Wq P p Cb χ δ ε f w c hΘ hw hχ hδχ hε.1 hf).1 hε.2]
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have h := GlobalTheory.T.topVector_cutoff_eq_and_vanish Wp Wq P p Cb χ δ ε f w c hΘ hw hχ hδχ hε' hf
    rw [h.2.1 ((not_lt.1 hG).trans_lt (mul_pos hδ hε')), h.2.2 (not_lt.1 hG)]

end GlobalTheory.TopVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WaveGridLiftGridOfLayoutNormaliserBoundStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.waveGrid_liftGrid_of_layout_normaliserBound : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (Λ Λ₀ : ℝ) (K N : ℕ), (∀ y, 0 < nn y) → ((∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|) ∧ N * (2 * P.r + 1) ≤ Y.card ∧ ∀ y ∈ Y, I.OnCut P.u P.u' p.l0 y ∧ I.OnCut P.u P.u' p.l0 (y + 1)) → (∀ y ∈ Y, nn y * nn (y + 1) ≤ Λ₀ ^ 2 * (M.qC P (y : ℂ)).re) → 0 ≤ Λ → Λ₀ ^ 2 * (5 / 4 : ℝ) ^ N ≤ Λ ^ 2 → TBBx5.WaveGrid p nn Y Λ K N ∧ TBBx5.LiftGrid p nn Y Λ K N := by
  first | exact @GlobalTheory.GridsFromLayout.main | exact GlobalTheory.GridsFromLayout.main | (intros; apply GlobalTheory.GridsFromLayout.main <;> assumption)
end

