module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0652
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIndepBridge
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0473
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateNoTwistedInvariantsComplexPadic
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalHeisenbergSpanPreservesTypeRelations
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.PlaceTranslate

variable {D : D7}

theorem mt_mul' (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by simp [Formalism.L2.Theta.mt]

theorem mt_one' (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem mul_mt_eq {S T : HSp D} {e : AE D} {g : GA D S} (hg : ∀ i j, e * (mt S g - 1) i j = 0) {u : WO S T}
    (hu : IsHalf e u) : HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g) = u := by
  have hM : ∀ k j, e * mt S g k j = e * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j := by
    intro k j
    have h := hg k j
    rw [Matrix.sub_apply, mul_sub, sub_eq_zero] at h
    exact h
  ext i j
  rw [Matrix.mul_apply]
  conv_rhs => rw [← Matrix.mul_one (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)), Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc u i k * mt S g k j = (e * u i k) * mt S g k j := by rw [hu i k]
    _ = u i k * (e * mt S g k j) := by ring
    _ = u i k * (e * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j) := by rw [hM k j]
    _ = (e * u i k) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j := by ring
    _ = u i k * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j := by rw [hu i k]

theorem actO_fix {S T : HSp D} {e : AE D} {g : GA D S} (hg : ∀ i j, e * (mt S g - 1) i j = 0) {u : WO S T}
    (hu : IsHalf e u) : actO S T g 1 u = u ∧ actO S T g⁻¹ 1 u = u := by
  have h1 := mul_mt_eq (T := T) hg hu
  have h2 : HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) = u := by
    conv_lhs => rw [← h1]
    rw [Matrix.mul_assoc, ← mt_mul', mul_inv_cancel, mt_one', Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · simp only [actO, mt_one', Matrix.one_mul]; exact h2
  · simp only [actO, mt_one', Matrix.one_mul, inv_inv]; exact h1

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem avgW_add (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) (f g : WO (Vc D i) (Wc D i) → ℂ) :
    avgW R i t PP a tr ε κ (f + g) = avgW R i t PP a tr ε κ f + avgW R i t PP a tr ε κ g := by
  simp only [avgW, map_add (f := _), smul_add, Finset.sum_add_distrib]

theorem avgW_smul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) (c : ℂ) (f : WO (Vc D i) (Wc D i) → ℂ) :
    avgW R i t PP a tr ε κ (c • f) = c • avgW R i t PP a tr ε κ f := by
  simp only [avgW, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun g _ => smul_comm _ _ _

theorem avgW_zero (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) : avgW R i t PP a tr ε κ 0 = 0 := by
  simp only [avgW, map_zero, smul_zero, Finset.sum_const_zero]

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T' : HSp D) (u : WO S T') : heisO ψ S T' u 0 = 0 := by
  funext w; simp [heisO]

theorem locSpan_pres : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP →
    ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)),
    v ∈ Sb → ∀ (ε : AF D.host.F) (a : AE D), IsPlaceIdem D v ε → a + cA D a = algebraMap (AF D.host.F) (AE D) ε →
    ∀ f : WO (Vc D i) (Wc D i) → ℂ, TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f →
    ∀ f' ∈ locSpan R.ψ (Vc D i) (Wc D i) a f,
      TypeIn R i t (dropPl Sb v) f' ∧ CleanIn R i t (dropPl Sb v) f' ∧ LikeOff R i t Sb f' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hω i t Sb v hv ε a hε hae f hT hC hL f' hf'
  set E' := algebraMap (AF D.host.F) (AE D) ε with hE'
  have hW := hω i t
  have hψ := hW.std
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := hT.1
  have hvd : v ∉ dropPl Sb v := by
    classical
    unfold dropPl
    simp
  have hsub : ∀ w, w ∈ dropPl Sb v → w ∈ Sb := by
    classical
    intro w hw
    unfold dropPl at hw
    exact Finset.mem_of_mem_erase hw

  have hsupp : ∀ κ : GA D (Vc D i), SuppIn (dropPl Sb v) (Vc D i) κ →
      SuppIn Sb (Vc D i) κ ∧ ∀ i' j', E' * (mt (Vc D i) κ - 1) i' j' = 0 := by
    intro κ hκ
    exact ⟨⟨hκ.1, fun w hw => hκ.2 w fun h => hw (hsub w h)⟩, hκ.2 v hvd ε hε⟩
  have hcE : cA D E' = E' := by
    rw [← hae, map_add (f := _), GlobalTheory.DualPairCheck.cA_cA, add_comm]

  let P : (WO (Vc D i) (Wc D i) → ℂ) → Prop := fun φ =>
    TypeIn R i t (dropPl Sb v) φ ∧ CleanIn R i t (dropPl Sb v) φ ∧ LikeOff R i t Sb φ
  have hgen : ∀ u : WO (Vc D i) (Wc D i), IsHalf E' u → P (heisO R.ψ (Vc D i) (Wc D i) u f) := by
    intro u hu
    have hthu := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hth u
    refine ⟨⟨hthu, fun κ hκ hκs => ?_⟩, ?_, ⟨hthu, ?_⟩⟩
    · obtain ⟨hκS, hκv⟩ := hsupp κ hκs
      rw [hW.om_heis κ 1 u f hth, (actO_fix hκv hu).1, hT.2 κ hκ hκS, GlobalTheory.SplitScalar.heisO_smul]
    · intro PP a' ha' tr e he hex κ hκ hκs
      have hex' : ∃ w ∈ Sb, Over PP.1 w := by
        obtain ⟨w, hw, hO⟩ := hex; exact ⟨w, hsub w hw, hO⟩
      have hκs' : ∀ g, mirC R i PP a' tr e g ≠ 0 → SuppIn Sb (Vc D i) (κ g) := fun g hg => (hsupp _ (hκs g hg)).1
      have key : avgW R i t PP a' tr e κ (heisO R.ψ (Vc D i) (Wc D i) u f) =
          heisO R.ψ (Vc D i) (Wc D i) u (avgW R i t PP a' tr e κ f) := by
        simp only [avgW]
        rw [GlobalTheory.SplitScalar.heisO_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        by_cases hc : mirC R i PP a' tr e g = 0
        · rw [hc, zero_mul, zero_smul, zero_smul, heisO_zero']
        · rw [hW.om_heis (κ g)⁻¹ 1 u f hth, (actO_fix (hsupp _ (hκs g hc)).2 hu).2, GlobalTheory.SplitScalar.heisO_smul]
      rw [key, hC PP a' ha' tr e he hex' κ hκ hκs', heisO_zero']
    · intro c hc h0
      have hcomm : ∀ w ∈ c.support, heisO R.ψ (Vc D i) (Wc D i) w (heisO R.ψ (Vc D i) (Wc D i) u f) =
          heisO R.ψ (Vc D i) (Wc D i) u (heisO R.ψ (Vc D i) (Wc D i) w f) := by
        intro w hw
        have hw0 : E' • w = 0 := by
          ext i' j'; exact (hc w hw).2 v hv ε hε i' j'
        have hs : symplO (Vc D i) (Wc D i) w u = 0 := by
          have hu' : E' • u = u := (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hu
          rw [← hu', ← hcE, ← GlobalTheory.SplitScalar.symplO_smul, hw0, GlobalTheory.SplitScalar.symplO_zero_left]
        rw [GlobalTheory.SplitScalar.heisO_comm, hs, AddChar.map_zero_eq_one, one_smul]
      have e1 : (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w (heisO R.ψ (Vc D i) (Wc D i) u f)) =
          heisO R.ψ (Vc D i) (Wc D i) u (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w f) := by
        unfold Finsupp.sum
        rw [GlobalTheory.SplitScalar.heisO_sum]
        refine Finset.sum_congr rfl fun w hw => ?_
        dsimp only
        rw [hcomm w hw, GlobalTheory.SplitScalar.heisO_smul]
      rw [e1, hL.2 c hc h0, heisO_zero']
  have h0 : P 0 := by
    have hz : IsThetaFunO R.ψ (Vc D i) (Wc D i) 0 := by simpa using theta_smul (0 : ℂ) hth
    refine ⟨⟨hz, fun κ _ _ => by rw [map_zero, smul_zero]⟩, fun _ _ _ _ _ _ _ _ _ _ => avgW_zero _ _ _ _ _ _ _ _,
      ⟨hz, fun c _ _ => ?_⟩⟩
    simp [heisO_zero']
  have hadd : ∀ φ₁ φ₂, P φ₁ → P φ₂ → P (φ₁ + φ₂) := by
    rintro φ₁ φ₂ ⟨⟨t1, T1⟩, C1, ⟨l1, L1⟩⟩ ⟨⟨t2, T2⟩, C2, ⟨l2, L2⟩⟩
    refine ⟨⟨theta_add t1 t2, fun κ hκ hκs => ?_⟩, fun PP a' ha' tr e he hex κ hκ hκs => ?_,
      ⟨theta_add l1 l2, fun c hc h0 => ?_⟩⟩
    · rw [map_add (f := _), T1 κ hκ hκs, T2 κ hκ hκs, smul_add]
    · rw [avgW_add, C1 PP a' ha' tr e he hex κ hκ hκs, C2 PP a' ha' tr e he hex κ hκ hκs, add_zero]
    · simp only [heisO_add', smul_add]
      rw [Finsupp.sum_add, L1 c hc h0, L2 c hc h0, add_zero]
  have hsmul : ∀ (r : ℂ) φ, P φ → P (r • φ) := by
    rintro r φ ⟨⟨t1, T1⟩, C1, ⟨l1, L1⟩⟩
    refine ⟨⟨theta_smul r t1, fun κ hκ hκs => ?_⟩, fun PP a' ha' tr e he hex κ hκ hκs => ?_,
      ⟨theta_smul r l1, fun c hc h0 => ?_⟩⟩
    · rw [map_smul, T1 κ hκ hκs, smul_comm]
    · rw [avgW_smul, C1 PP a' ha' tr e he hex κ hκ hκs, smul_zero]
    · have e1 : (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w (r • φ)) =
          r • (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w φ) := by
        rw [Finsupp.smul_sum]
        refine Finsupp.sum_congr fun w _ => ?_
        rw [GlobalTheory.SplitScalar.heisO_smul, smul_comm]
      rw [e1, L1 c hc h0, smul_zero]
  refine Submodule.span_induction (p := fun φ _ => P φ) ?_ h0 (fun x y _ _ hx hy => hadd x y hx hy)
    (fun r x _ hx => hsmul r x hx) hf'
  rintro φ ⟨u, hu, rfl⟩
  rw [hae] at hu
  exact hgen u hu

end GlobalTheory.DownLift.PlaceTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionCharacterTwist
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.ExtTwist

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpTwist_lpTwist_comm (x : WD h) (ξ η : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ)
    (hη : WeilDeligne.IsSmooth η) : (x.lpTwist ξ hξ).lpTwist η hη = (x.lpTwist η hη).lpTwist ξ hξ := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  simp only [WD.lpTwist_mk]
  exact WD.sound ⟨LinearEquiv.refl ℂ _, fun σ v => smul_comm (η σ : ℂ) (ξ σ : ℂ) (b.ρ σ v), fun v => rfl⟩

theorem hasCentralChar_ofChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : HasCentralChar (IrrGL.ofChar χ hχ).rep χ := fun z v => by
  let φ := equivRep (IrrRep.det (Fin 1) χ hχ)
  obtain ⟨u, rfl⟩ := φ.toLinearEquiv.surjective v
  have h2 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z) = z := by
    ext; simp [GeneralLinearGroup.scalar]
  have h3 : (IrrRep.det (Fin 1) χ hχ).ρ (GeneralLinearGroup.scalar (Fin 1) z) u = (χ z : ℂ) • u := by
    show (χ (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z)) : ℂ) • u = _
    rw [h2]
  show (IrrRep.det (Fin 1) χ hχ).cl.rep.ρ (GeneralLinearGroup.scalar (Fin 1) z) (φ.toIntertwiningMap u) =
    _ • φ.toIntertwiningMap u
  rw [← φ.toIntertwiningMap.isIntertwining, h3, map_smul]
  rfl

end GlobalTheory.LocLanglands.ExtTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemClosureOfJumps
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

namespace GlobalTheory.HodgeTateCochar

theorem poly_vanish : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL K'' : FinExt l) (m : ℕ) (r₁ : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1),
    LL.1 ≤ K''.1 → K.1 ≤ K''.1 → ∀ (Pm : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) (k : Fin m → ℤ),
    (∀ g : ↥(GK K), (g : GQ l) ∈ GK K'' →
      (r₁ g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) *
        (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) =
      (Pm : Matrix (Fin m) (Fin m) ℂ_[l]) *
        Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]))) →
    ∀ f : MvPolynomial (Fin m × Fin m) ℂ_[l],
    (∀ g : ↥(GK K), (g : GQ l) ∈ GK K'' →
      MvPolynomial.eval (fun ij => ((((r₁ g : Matrix (Fin m) (Fin m) ↥LL.1) ij.1 ij.2 : ↥LL.1) : Om l) : ℂ_[l])) f = 0) →
    ∀ t : ℂ_[l], t ≠ 0 →
      MvPolynomial.eval (fun ij => ((Pm : Matrix (Fin m) (Fin m) ℂ_[l]) * Matrix.diagonal (fun i => t ^ k i) *
        ((Pm⁻¹ : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) : Matrix (Fin m) (Fin m) ℂ_[l])) ij.1 ij.2) f = 0 := by
  intro l _ P AI hT K LL K'' m r₁ hLL hK Pm k heig f hf t ht
  letI act : MulSemiringAction ↥(GK K'') ℂ_[l] :=
    { smul := fun g x => Per.σC (g : GQ l) x
      one_smul := fun x => GlobalTheory.RingBasics.σC_one x
      mul_smul := fun g h x => GlobalTheory.RingBasics.σC_mul (g : GQ l) (h : GQ l) x
      smul_zero := fun g => map_zero (Per.σC (g : GQ l))
      smul_add := fun g x y => map_add (Per.σC (g : GQ l)) x y
      smul_one := fun g => map_one (Per.σC (g : GQ l))
      smul_mul := fun g x y => map_mul (Per.σC (g : GQ l)) x y }
  let χ : ↥(GK K'') →* ℂ_[l]ˣ :=
    ((Units.map (algebraMap ℚ_[l] ℂ_[l]).toMonoidHom).comp (P.χQ.comp (GK K'').subtype))⁻¹
  have hχ : ∀ (g : ↥(GK K'')) (n : ℤ), ((χ g ^ n : ℂ_[l]ˣ) : ℂ_[l]) =
      ((((P.χQ (g : GQ l)) ^ (-n) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) := by
    intro g n
    have e : χ g ^ n = Units.map (algebraMap ℚ_[l] ℂ_[l]).toMonoidHom (P.χQ (g : GQ l) ^ (-n)) := by
      rw [map_zpow]
      simp [χ, zpow_neg, inv_zpow']
    rw [e]
    rfl
  let φ : ↥LL.1 →+* ℂ_[l] := (UniformSpace.Completion.coeRingHom).comp (algebraMap ↥LL.1 (Om l))
  let ρ : ↥(GK K'') →* Matrix.GeneralLinearGroup (Fin m) ℂ_[l] :=
    (mapRep φ r₁).comp (Subgroup.inclusion (GK_le hK))
  have hρ : ∀ (γ : ↥(GK K'')) i j, (ρ γ : Matrix (Fin m) (Fin m) ℂ_[l]) i j =
      ((((r₁ (Subgroup.inclusion (GK_le hK) γ) : Matrix (Fin m) (Fin m) ↥LL.1) i j : ↥LL.1) : Om l) : ℂ_[l]) :=
    fun _ _ _ => rfl
  have key := _root_.GlobalTheory.HTCPoly.vanish_at_cocharacter (C := ℂ_[l]) (Γ := ↥(GK K'')) (n := Fin m) χ ?_ ρ ?_ Pm k ?_ f ?_ (Units.mk0 t ht)
  · simpa [Units.val_zpow_eq_zpow_val] using key
  · intro n hn x H
    refine _root_.GlobalTheory.TateChiQ.tate_chiQ l P AI hT K'' (-n) (neg_ne_zero.mpr hn) x fun g => ?_
    exact (H g).trans (by rw [hχ])
  · intro g γ i j
    change Per.σC (g : GQ l) _ = _
    rw [hρ, GlobalTheory.RingBasics.σC_coe]
    congr 1
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (hLL (r₁ _ i j).2)
  · intro g
    have h1 := heig (Subgroup.inclusion (GK_le hK) g) g.2
    change (ρ g : Matrix (Fin m) (Fin m) ℂ_[l]) * (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) = _
    simp only [hχ]
    exact h1
  · intro γ
    exact hf _ γ.2

theorem mem_closure_of_jumps : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) {a : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin a) (Om l)) (τ : E →+* Om l) (J : Multiset ℤ), GlobalTheory.Pst.IsJumpsAt P Bw r τ J → Multiset.card J = a → ∃ (Pm : Matrix.GeneralLinearGroup (Fin a) ℂ_[l]) (k : Fin a → ℤ), Multiset.map k Finset.univ.val = J ∧ ∀ (K' : FinExt l), Bw.Kw.1 ≤ K'.1 → ∀ f : MvPolynomial (Fin a × Fin a) ℂ_[l], (∀ g : ↥Gw, ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) ∈ GK K' → MvPolynomial.eval (fun ij => (((r g : Matrix (Fin a) (Fin a) (Om l)) ij.1 ij.2 : Om l) : ℂ_[l])) f = 0) → ∀ t : ℂ_[l], t ≠ 0 → MvPolynomial.eval (fun ij => ((Pm : Matrix (Fin a) (Fin a) ℂ_[l]) * Matrix.diagonal (fun i => t ^ k i) * ((Pm⁻¹ : Matrix.GeneralLinearGroup (Fin a) ℂ_[l]) : Matrix (Fin a) (Fin a) ℂ_[l])) ij.1 ij.2) f = 0 := by
  intro l _ P AI hT E Ω _ _ _ _ Gw O _ _ _ Bw a r τ J hJ hcard
  obtain ⟨LL', r', ⟨hLL, hmod⟩, hdR, τ', -, hcnt⟩ := hJ
  haveI := Bw.Kw.2
  haveI := LL'.2

  let τo : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l := LL'.1.val.comp τ'
  let g : GQ l := AlgEquiv.ofBijective (τo.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _)
  have hg : ∀ x : ↥Bw.Kw.1, g (x : Om l) = ((τ' x : ↥LL'.1) : Om l) := fun x => τo.liftNormal_commutes (Om l) x

  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : FinExt l, K₁.1 = Bw.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l) :=
    ⟨⟨Bw.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l),
      LinearEquiv.finiteDimensional (IntermediateField.equivMap Bw.Kw.1 (g : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv⟩, rfl⟩
  have hK : ∀ x, x ∈ Bw.Kw.1 ↔ g x ∈ K₁.1 := GlobalTheory.Pst.BridgeInd.mem_iff_of_map_eq hK₁
  have hK₁LL : K₁.1 ≤ LL'.1 := by
    rw [hK₁]
    rintro _ ⟨x, hx, rfl⟩
    have := hg ⟨x, hx⟩
    simp only at this
    change g x ∈ LL'.1
    rw [this]; exact (τ' ⟨x, hx⟩).2

  let cj : ↥(GK K₁) →* ↥(GK Bw.Kw) :=
    { toFun := fun h => ⟨g⁻¹ * (h : GQ l) * g, GlobalTheory.Pst.BridgeInd.mem_GK_conj_inv hK h.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun h₁ h₂ => Subtype.ext (by simp [mul_assoc]) }
  let r₀ : ↥(GK Bw.Kw) →* Matrix.GeneralLinearGroup (Fin a) ↥LL'.1 := r'.comp Bw.e.symm.toMonoidHom
  let r₁ : ↥(GK K₁) →* Matrix.GeneralLinearGroup (Fin a) ↥LL'.1 := r₀.comp cj
  have hρ : ∀ (h : ↥(GK Bw.Kw)) (h' : ↥(GK K₁)), (h' : GQ l) = g * h * g⁻¹ →
      (((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp
        ((Units.coeHom _).comp r₁)) h' = Bw.repE LL' r' h := by
    intro h h' hh
    have : cj h' = h := Subtype.ext (by simp [cj, hh, mul_assoc])
    simp only [MonoidHom.comp_apply, r₁, this]
    rfl
  have hD := GlobalTheory.Pst.BridgeInd.finrank_DdR_conj P hρ hK
  have hdR₁ : Module.finrank ↥LL'.1 ↥(DdR (P.PD K₁) (LL := ↥LL'.1) (V := Fin a → ↥LL'.1) (((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp
        ((Units.coeHom _).comp r₁))) = Module.finrank ℚ_[l] ↥K₁.1 * a := by
    rw [← hD, ← GlobalTheory.Pst.BridgeInd.finrank_eq_of_mem_iff_field hK]
    exact hdR
  let τ₂ : ↥K₁.1 →ₐ[ℚ_[l]] ↥LL'.1 := IntermediateField.inclusion hK₁LL
  have hτ₂ : ∀ x : ↥K₁.1, ((τ₂ x : ↥LL'.1) : Om l) = (x : Om l) := fun x => rfl
  have hM : ∀ n, multV (P.PD Bw.Kw) (Bw.repE LL' r') τ' n = multV (P.PD K₁) _ τ₂ n :=
    fun n => GlobalTheory.Pst.BridgeInd.multV_conj P hρ hK τ' τ₂ (fun c c' hc => Subtype.ext (by
      change (c' : Om l) = _; rw [hc, hg])) n
  have hsplit : ∀ (σ : ↥K₁.1 →ₐ[ℚ_[l]] Om l) (x : ↥K₁.1), σ x ∈ LL'.1 := by
    intro σ x
    have hx : g⁻¹ (x : Om l) ∈ Bw.Kw.1 := (hK _).2 (by simp)
    let e₁ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥K₁.1 :=
      ((g : Om l →ₐ[ℚ_[l]] Om l).comp Bw.Kw.1.val).codRestrict K₁.1.toSubalgebra fun c => (hK _).1 c.2
    have he : e₁ ⟨g⁻¹ (x : Om l), hx⟩ = x := Subtype.ext (by
      change g (g⁻¹ (x : Om l)) = (x : Om l)
      rw [← AlgEquiv.mul_apply, mul_inv_cancel]; rfl)
    rw [← he]
    exact hLL (Bw.LL_split (σ.comp e₁) ⟨g⁻¹ (x : Om l), hx⟩)
  haveI := K₁.2
  let K₀ : FinExt l := ⟨K₁.1 ⊔ LL'.1, inferInstance⟩
  obtain ⟨Pm, k, hk, heig⟩ := GlobalTheory.T.deRham_exists_hodgeTate_eigenbasis l P AI hT K₁ LL' a r₁ hdR₁ hsplit τ₂ hτ₂ K₀
    le_sup_left le_sup_right
  refine ⟨Pm, k, ?_, ?_⟩
  · refine Multiset.ext.mpr fun n => ?_
    have := (hk n).trans ((hM n).symm.trans (hcnt n).symm)
    exact_mod_cast this
  intro K' hK' f hf t ht
  haveI := K'.2
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : FinExt l, K₂.1 = K'.1.map (g : Om l →ₐ[ℚ_[l]] Om l) :=
    ⟨⟨K'.1.map (g : Om l →ₐ[ℚ_[l]] Om l),
      LinearEquiv.finiteDimensional (IntermediateField.equivMap K'.1 (g : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv⟩, rfl⟩
  have hK' : ∀ x, x ∈ K'.1 ↔ g x ∈ K₂.1 := GlobalTheory.Pst.BridgeInd.mem_iff_of_map_eq hK₂
  haveI := K₂.2
  let K'' : FinExt l := ⟨K₂.1 ⊔ K₀.1, inferInstance⟩
  refine poly_vanish l P AI hT K₁ LL' K'' a r₁ (le_trans le_sup_right le_sup_right)
    (le_trans le_sup_left le_sup_right) Pm k (fun h hh => heig h (GK_le le_sup_right hh)) f ?_ t ht
  intro h hh
  have h2 : (h : GQ l) ∈ GK K₂ := GK_le le_sup_left hh
  have h3 : ((cj h : ↥(GK Bw.Kw)) : GQ l) ∈ GK K' := GlobalTheory.Pst.BridgeInd.mem_GK_conj_inv hK' h2
  have h4 := hf (Bw.e.symm (cj h)) (by simpa using h3)
  rw [← hmod] at h4
  exact h4

end GlobalTheory.HodgeTateCochar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicHyperplaneAverageSupportResidueGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

section Reindex
variable {n K L : Type} [Fintype n] [CommRing K] [CommRing L]

theorem map_symm_mulVec_comp (ρ : K ≃+* L) (M : Matrix n n L) (x : n → L) :
    (M.map ρ.symm) *ᵥ (fun j => ρ.symm (x j)) = fun j => ρ.symm ((M *ᵥ x) j) := by
  funext j
  exact (RingHom.map_mulVec ρ.symm.toRingHom M x j).symm

theorem fix_hyperplane_map_iff (ρ : K ≃+* L) (M : Matrix n n L) (a : n → K) :
    (∀ x, (fun j => ρ (a j)) ⬝ᵥ x = 0 → M *ᵥ x = x) ↔ ∀ w, a ⬝ᵥ w = 0 → (M.map ρ.symm) *ᵥ w = w := by
  constructor
  · intro h w hw
    have hd : (fun j => ρ (a j)) ⬝ᵥ (fun j => ρ (w j)) = 0 := by
      have := (RingHom.map_dotProduct ρ.toRingHom a w).symm
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hw, map_zero] at this
      exact this
    have h1 := h _ hd
    have h2 := map_symm_mulVec_comp ρ M (fun j => ρ (w j))
    rw [h1] at h2
    simpa only [RingEquiv.symm_apply_apply] using h2
  · intro h x hx
    have hd : a ⬝ᵥ (fun j => ρ.symm (x j)) = 0 := by
      have := (RingHom.map_dotProduct ρ.symm.toRingHom (fun j => ρ (a j)) x).symm
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hx, map_zero] at this
      simpa only [Function.comp_def, RingEquiv.symm_apply_apply] using this
    have h1 := h _ hd
    rw [map_symm_mulVec_comp] at h1
    funext j
    have := congrArg ρ (congrFun h1 j)
    simpa only [RingEquiv.apply_symm_apply] using this

end Reindex

theorem mirC_hyperplane_reindex : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (PP : Pl D.host.E) (hPP : PP ∈ R.Pg) (v : FinPl D) (ρk : IsLocalRing.ResidueField (OI v) ≃+* kP PP) (a : Fin D.R.r → IsLocalRing.ResidueField (OI v)) (F : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) → ℂ), (∑ᶠ g ∈ {g : G | mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0}, F (Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g ⟨PP, hPP⟩))) = ∑ᶠ g ∈ {g : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) | ∀ w, a ⬝ᵥ w = 0 → (g : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (OI v))).mulVec w = w}, F g := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R i PP hPP v ρk a F
  set P : R.Pg := ⟨PP, hPP⟩ with hP
  have key : ∀ g : G, ((∀ x, (fun j => ρk (a j)) ⬝ᵥ x = 0 →
      ((R.eG g P : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) *ᵥ x = x) ↔
      ∀ w, a ⬝ᵥ w = 0 → ((Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g P) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) _) *ᵥ w = w) :=
    fun g => fix_hyperplane_map_iff ρk _ a
  have hset : {g : G | mirC R i P (fun j => ρk (a j)) false 1 g ≠ 0} =
      {g : G | (∀ PP', PP' ≠ P → R.eG g PP' = 1) ∧ ∀ w, a ⬝ᵥ w = 0 →
        ((Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g P) : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) *ᵥ w = w} := by
    ext g
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ← key g]
    simp only [mirC, Bool.false_eq_true, ↓reduceIte, zpow_one]
    split_ifs with hc
    · simp only [ne_eq, Units.ne_zero, not_false_eq_true, true_iff]
      exact hc
    · simp only [ne_eq, not_true_eq_false, false_iff]
      exact hc
  rw [hset]
  apply finsum_mem_eq_of_bijOn (fun g => Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g P))
  · refine ⟨?_, ?_, ?_⟩
    · rintro g ⟨_, hg⟩
      exact hg
    · rintro g₁ ⟨h1, _⟩ g₂ ⟨h2, _⟩ he
      apply R.eG.injective
      funext PP'
      by_cases hq : PP' = P
      · rw [hq]
        have he' : ((R.eG g₁ P : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)).map ρk.symm =
            ((R.eG g₂ P : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)).map ρk.symm :=
          congrArg Units.val he
        exact Units.ext (Matrix.map_injective ρk.symm.injective he')
      · rw [h1 PP' hq, h2 PP' hq]
    · intro g₀ hg₀
      have hcomp : Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (Matrix.GeneralLinearGroup.map ρk.toRingHom g₀) = g₀ := by
        ext j k
        simp
      refine ⟨R.eG.symm (Pi.mulSingle P (Matrix.GeneralLinearGroup.map ρk.toRingHom g₀)), ⟨?_, ?_⟩, ?_⟩
      · intro PP' hq
        rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_of_ne hq]
      · rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same, hcomp]
        exact hg₀
      · show Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG (R.eG.symm _) P) = g₀
        rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same, hcomp]
  · intro g _
    rfl

end GlobalTheory.DownLift.GenSplit

end
end

