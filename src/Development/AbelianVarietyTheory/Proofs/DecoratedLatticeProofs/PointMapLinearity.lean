module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerFockProductEqProdRealPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockCoefficientRealPlaceTwoVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section
namespace GlobalTheory.FockCoefIndep

section Place
open GlobalTheory.ArchRec GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.VacCoefAtPlace

theorem uniform_place : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ∀ (m : Measure (WO V W)) (X : Set (WO V W)), IsCovolOne (ratL W V) m X → ∀ (τ : D.what₂.Tau) (a : ℚ), ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ P Q : LPol W.rank V.rank, ∃ K : ℂ, ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → HasInfExp D χT τ a → ∀ x y : WO V W → ℂ, IsThetaFunO ψ V W x → IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) x → IsThetaFunO ψ V W y → IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) y → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (atTau θ V τ g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) x P)) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) y Q) = K * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X x y := by
  intro D V W S S' M M' θ ψ hθ m X hX τ a g hg P Q
  have hK0 : ∃ K : ℂ, ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
      IsWeilDatumO ψ V W χS χT ω → HasInfExp D χT τ a → ∀ f, IsThetaFunO ψ V W f →
      IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f → f ≠ 0 →
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X
                   (ω (atTau θ V τ g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) f P))
                   (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) f Q) =
        GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f * K := by
    obtain ⟨hμ, h𝓕, -⟩ := id hX
    have fS := isFrameOf_model M τ
    have fT := isFrameOf_model M' τ
    obtain ⟨p, q, e, he⟩ := exists_signCompat (M.ε τ)
    obtain ⟨r, s, e', he'⟩ := exists_signCompat (M'.ε τ)
    by_cases hn : 1 ≤ p + q
    · by_cases hint : ∃ n : ℤ, (n : ℚ) = 2 * a
      swap
      · refine ⟨0, fun χS χT ω hω haT => ?_⟩
        obtain ⟨n, hn2, -⟩ := haT
        exact (hint ⟨n, hn2⟩).elim
      obtain ⟨mT, hmT⟩ := hint
      obtain ⟨κ, k1, -, k3⟩ := GlobalTheory.ArchRec.SignedRename.exists_isPolyIso_graded_isometry p q r s _ _ (M.ε τ) (M'.ε τ)
        e e' he he'
      obtain ⟨T₀⟩ := GlobalTheory.DetSqrtCover.nonempty_grpData (p * r + q * s) (p * s + q * r)
      obtain ⟨T₁⟩ := GlobalTheory.DetSqrtCover.nonempty_grpData p q
      obtain ⟨T₂⟩ := GlobalTheory.DetSqrtCover.nonempty_grpData r s
      obtain ⟨F⟩ := GlobalTheory.nonempty_fockData_pair p q r s T₀ T₁ T₂
      obtain ⟨g₁, hg₁⟩ := exists_cov T₁ (M.fr_unit τ) (M.fr_gram τ) he hg
      refine ⟨((T₁.sq g₁ : ℂˣ) : ℂ) ^ mT * ⟪F.ι (κ Q), F.π (g₁, 1) (F.ι (κ P))⟫_ℂ,
        fun χS χT ω hω haT f hf hv h0 => ?_⟩
      have hψ := hω.std
      obtain ⟨aS, haS⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D θ χS _ τ hθ hω.hecS hω.resS
      obtain ⟨c1, c2⟩ := GlobalTheory.OnePlaceFock.fock_at_one_place D ψ θ V W τ hψ hθ _ _ _ _ _ _ fS fT f hf hv
      obtain ⟨cinj, c3⟩ := c2 h0
      obtain ⟨N, n1, n2⟩ := c3 m X hμ h𝓕
      have hL := GlobalTheory.ArchRec.LieAtPlace.lieAt_of_vacAt D ψ θ V W χS χT ω τ hθ hω aS a haS haT _ _ _ _ _ _ fS fT f hf hv
      let pt : LPol W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorL (fun k : Fin W.rank × Fin V.rank =>
        aPlus (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) (unitMap (M.fr τ)⁻¹ (M'.fr τ)⁻¹ k.1 k.2)) f
      obtain ⟨s1, -⟩ := GlobalTheory.ArchRec.SideAt.side_at D ψ θ V W ω τ hθ _ _ _ _ _ _ fS fT aS a pt cinj hL p q r s e e' he he'
        κ k1
      obtain ⟨Θ, t1, -⟩ := GlobalTheory.ThetaL2InnerProduct.exists_l2_unitary_theta_of_fundamentalDomain D ψ θ V W χS χT ω τ hθ hω (M.fr τ) (M.ε τ) (M'.fr τ) (M'.ε τ)
        aS a pt c1 hL m X hμ h𝓕
      have hF : Fischer pt (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X) κ N :=
        ⟨n1, fun P Q => by rw [k3]; exact n2 P Q⟩
      have hC := GlobalTheory.ArchRec.FockCoef.coef_of_side p q r s V.rank T₀ T₁ T₂ F _ _ (gramAt D V τ) (M.fr τ) (M.ε τ) true e
        (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.actSrc θ ω τ) pt (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X) Θ κ a mT N hn (M.fr_unit τ) (M.fr_gram τ) he hmT s1 t1 hF
      have hN : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f = N := by
        have := n2 1 1
        rw [LinearEquiv.refl_apply, fockIp_one, mul_one] at this
        simpa only [GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt, GlobalTheory.FockIndep.pure_one] using this
      have h2 := hC.2.2 g₁ P Q
      rw [hg₁] at h2
      rw [hN, ← mul_assoc]
      exact h2
    · have hV : V.rank = 0 := by
        have := Fintype.card_congr e
        simp at this
        omega
      have g1 : g = 1 := by
        ext i j
        have := i.2
        omega
      refine ⟨fockIp P Q, fun χS χT ω hω _ f hf hv h0 => ?_⟩
      have hψ := hω.std
      obtain ⟨-, c2⟩ := GlobalTheory.OnePlaceFock.fock_at_one_place D ψ θ V W τ hψ hθ _ _ _ _ _ _ fS fT f hf hv
      obtain ⟨-, c3⟩ := c2 h0
      obtain ⟨N, -, n2⟩ := c3 m X hμ h𝓕
      have hN : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f = N := by
        have := n2 1 1
        rw [LinearEquiv.refl_apply, fockIp_one, mul_one] at this
        simpa only [GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt, GlobalTheory.FockIndep.pure_one] using this
      rw [g1, GlobalTheory.PointAtPlaceHom.atTau_one hθ, Prod.mk_one_one, map_one, one_apply_eq_self, hN]
      exact n2 P Q
  obtain ⟨K, hK⟩ := hK0
  refine ⟨K, fun χS χT ω hω haT x y hx vx hy vy => ?_⟩
  have hψ := hω.std
  obtain ⟨hμ, h𝓕, -⟩ := id hX
  let pt := GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ)
  let vac : (WO V W → ℂ) → Prop := fun x =>
    IsThetaFunO ψ V W x ∧ IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) x
  have th : ∀ x y, vac x → vac y → IsThetaFunO ψ V W (ω (atTau θ V τ g, 1) (pt x P)) ∧ IsThetaFunO ψ V W (pt y Q) :=
    fun x y hx hy => ⟨hω.om_pres _ _ (ptAt_theta hψ hθ _ _ _ _ _ hx.1 P), ptAt_theta hψ hθ _ _ _ _ _ hy.1 Q⟩
  have hv : ∀ (a : ℂ) x y, vac x → vac y → vac (a • x + y) := fun a x y hx hy =>
    ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul a hx.1) hy.1, vac_lin hψ hθ τ _ a hx.1 hy.1 hx.2 hy.2⟩
  let E : (WO V W → ℂ) → (WO V W → ℂ) → ℂ := fun x y =>
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (atTau θ V τ g, 1) (pt x P)) (pt y Q) - K * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X x y
  have h1 : ∀ (a : ℂ) x y z, vac x → vac y → vac z → E (a • x + y) z = a * E x z + E y z := by
    intro a x y z hx hy hz
    simp only [E, pt]
    rw [ptAt_lin hψ hθ _ _ _ _ _ a hx.1 hy.1, map_add (f := _), map_smul]
    simp only [GlobalTheory.ThetaL2InnerProduct.ipTh_eq]
    rw [GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 (GlobalTheory.OrientedHeis.theta_smul a (th x z hx hz).1) (th y z hy hz).1
        (th x z hx hz).2, GlobalTheory.Size.ipO_smul_left,
      GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 (GlobalTheory.OrientedHeis.theta_smul a hx.1) hy.1 hz.1, GlobalTheory.Size.ipO_smul_left]
    ring
  have h2 : ∀ (a : ℂ) x y z, vac x → vac y → vac z → E z (a • x + y) = conj a * E z x + E z y := by
    intro a x y z hx hy hz
    simp only [E, pt]
    rw [ptAt_lin hψ hθ _ _ _ _ _ a hx.1 hy.1]
    simp only [GlobalTheory.ThetaL2InnerProduct.ipTh_eq]
    rw [GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 (th z x hz hx).1 (GlobalTheory.OrientedHeis.theta_smul a (th z x hz hx).2)
        (th z y hz hy).2, GlobalTheory.Size.ipO_smul_right,
      GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 hz.1 (GlobalTheory.OrientedHeis.theta_smul a hx.1) hy.1, GlobalTheory.Size.ipO_smul_right]
    ring
  have h0 : ∀ x, vac x → E x x = 0 := by
    intro x hx
    by_cases hx0 : x = 0
    · have z0 : ∀ R, pt 0 R = 0 := fun R => by
        have h := ptAt_lin hψ hθ τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) (-1)
          (GlobalTheory.ThetaL2InnerProduct.thetaSpace ψ V W).zero_mem (GlobalTheory.ThetaL2InnerProduct.thetaSpace ψ V W).zero_mem R
        rw [smul_zero, add_zero, neg_one_smul, neg_add_cancel] at h
        exact h
      simp only [E, hx0, z0, map_zero, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh]
      simp
    · simp only [E]
      rw [hK χS χT ω hω haT x hx.1 hx.2 hx0]
      ring
  exact sub_eq_zero.1 (polar hv E h1 h2 h0 ⟨hx, vx⟩ ⟨hy, vy⟩)

end Place

theorem uniform_glue : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ∀ (m : Measure (WO V W)) (X : Set (WO V W)), IsCovolOne (ratL W V) m X → ∀ (aT : D.what₂.Tau → ℚ) (P Q : D.what₂.Tau → LPol W.rank V.rank), ∀ g ∈ GinfC V, ∃ C : ℂ, ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → (∀ τ, HasInfExp D χT τ (aT τ)) → ∀ x y : WO V W → ℂ, IsThetaFunO ψ V W x → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) x) → IsThetaFunO ψ V W y → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) y) → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (GlobalTheory.Chain.ptOf ψ θ M M' x (GlobalTheory.Chain.RealIt.glue P))) (GlobalTheory.Chain.ptOf ψ θ M M' y (GlobalTheory.Chain.RealIt.glue Q)) = C * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X x y := by
  intro D V W S S' M M' θ ψ hθ m X hX aT
  classical
  let pt := fun ρ => GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W ρ (cart M ρ) (cart M' ρ) (onb M ρ) (onb M' ρ)
  let vac := fun ρ => IsFockVacAt (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ))

  have ptOf_theta (hψ : IsStdChar D ψ (-1)) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
      (P : PolF D W.rank V.rank) : IsThetaFunO ψ V W (GlobalTheory.Chain.ptOf ψ θ M M' f P) :=
    GlobalTheory.FockIndep.pure_mem
      (A := aPlusAll (heisO ψ V W) θ (fun τ => cplxO (cart M τ) (cart M' τ)) (onb M) (onb M'))
      (fun _ _ => GlobalTheory.WeilVacMove.isTheta_add)
      (fun c _ => GlobalTheory.WeilVacMove.isTheta_smul c)
      (fun i _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ i.1 _ _ h) hf P
  have ptOf_glue_one {f : WO V W → ℂ} (P : D.what₂.Tau → LPol W.rank V.rank) (hP : ∀ τ, P τ = 1) :
      GlobalTheory.Chain.ptOf ψ θ M M' f (GlobalTheory.Chain.RealIt.glue P) = f := by
    have h : GlobalTheory.Chain.RealIt.glue P = 1 := by
      unfold GlobalTheory.Chain.RealIt.glue
      exact Finset.prod_eq_one fun τ _ => by rw [hP τ, map_one]
    rw [h]
    exact GlobalTheory.FockIndep.pure_one f
  have ptOf_glue (hψ : IsStdChar D ψ (-1)) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
      (P : D.what₂.Tau → LPol W.rank V.rank) (τ : D.what₂.Tau) :
      GlobalTheory.Chain.ptOf ψ θ M M' f (GlobalTheory.Chain.RealIt.glue P) =
        pt τ (GlobalTheory.Chain.ptOf ψ θ M M' f (GlobalTheory.Chain.RealIt.glue (Function.update P τ 1))) (P τ) := by
    let A := aPlusAll (heisO ψ V W) θ (fun τ => cplxO (cart M τ) (cart M' τ)) (onb M) (onb M')
    have hAdd (g g' : WO V W → ℂ) (hg : IsThetaFunO ψ V W g) (hg' : IsThetaFunO ψ V W g') :
        IsThetaFunO ψ V W (g + g') := GlobalTheory.WeilVacMove.isTheta_add hg hg'
    have hSmul (c : ℂ) (g : WO V W → ℂ) (hg : IsThetaFunO ψ V W g) : IsThetaFunO ψ V W (c • g) :=
      GlobalTheory.WeilVacMove.isTheta_smul c hg
    have hA (i) (g) (hg : IsThetaFunO ψ V W g) : IsThetaFunO ψ V W (A i g) :=
      GlobalTheory.FockIndep.aPlus_theta hψ hθ i.1 _ _ hg
    have hComm (i j) (g) (hg : IsThetaFunO ψ V W g) : A i (A j g) = A j (A i g) :=
      GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _
        (GlobalTheory.Chain.VacVec.cart_isCartanInv M) (GlobalTheory.Chain.VacVec.cart_isCartanInv M') j.1 _ hg
    have hAAdd (i) (g g') (hg : IsThetaFunO ψ V W g) (hg' : IsThetaFunO ψ V W g') :
        A i (g + g') = A i g + A i g' := GlobalTheory.FockIndep.aPlus_add hψ hθ i.1 _ _ hg hg'
    have hASmul (i) (c : ℂ) (g) (hg : IsThetaFunO ψ V W g) : A i (c • g) = c • A i g :=
      GlobalTheory.FockIndep.aPlus_smul hψ hθ i.1 _ _ c hg
    rw [GlobalTheory.Chain.RealIt.GlueProof.glue_eq τ P,
      GlobalTheory.Chain.RealIt.GlueProof.glue_update τ P 1,
      GlobalTheory.Chain.RealIt.GlueProof.ins_apply, GlobalTheory.Chain.RealIt.GlueProof.ins_apply,
      map_one, one_mul]
    unfold GlobalTheory.Chain.ptOf pureTensorO
    rw [GlobalTheory.FockProdCoef.pure_mul hAdd hSmul hA hComm hAAdd hASmul hf,
      GlobalTheory.FockProdCoef.pure_rename hA hComm
        (GlobalTheory.FockIndep.pure_mem hAdd hSmul hA hf _)]
    rfl

  have peel (g : GA D V) (τ : D.what₂.Tau) :
      let a := atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) g)
      a ∈ GinfC V ∧ infMat D.sp.cm.sig V.gram (θ τ) (a⁻¹ * g) = 1 ∧
        ∀ ρ ≠ τ, infMat D.sp.cm.sig V.gram (θ ρ) (a⁻¹ * g) = infMat D.sp.cm.sig V.gram (θ ρ) g := by
    dsimp only
    have hu := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
    have ha := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hu
    set a := atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) g)
    have hinv (ρ : D.what₂.Tau) :
        infMat D.sp.cm.sig V.gram (θ ρ) a⁻¹ * infMat D.sp.cm.sig V.gram (θ ρ) a = 1 := by
      rw [← GlobalTheory.PointAtPlaceHom.infMat_mul, inv_mul_cancel, GlobalTheory.PointAtPlaceHom.infMat_one]
    refine ⟨ha.1, ?_, fun ρ hρ => ?_⟩
    · rw [GlobalTheory.PointAtPlaceHom.infMat_mul, ← ha.2.1]
      exact hinv τ
    · have h := hinv ρ
      rw [ha.2.2 ρ hρ, Matrix.mul_one] at h
      rw [GlobalTheory.PointAtPlaceHom.infMat_mul, h, Matrix.one_mul]
  have ginf_induction (p : GA D V → Prop) (hone : p 1) (hmul : ∀ a b, p a → p b → p (a * b))
      (A : Finset D.what₂.Tau)
      (hat : ∀ τ ∈ A, ∀ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), p (atTau θ V τ k)) :
      ∀ g ∈ GinfC V, (∀ τ ∉ A, infMat D.sp.cm.sig V.gram (θ τ) g = 1) → p g := by
    induction A using Finset.induction_on with
    | empty =>
      intro g hg hg1
      have h := (GlobalTheory.SmoothForms.RealPts.glue θ hθ V).1 g fun τ => hg1 τ (Finset.notMem_empty τ)
      rw [GlobalTheory.PointAtPlace.eq_one_of_mem V g h hg]
      exact hone
    | insert τ A hτ ih =>
      intro g hg hg1
      obtain ⟨ha, hs, ho⟩ := peel g τ
      set a := atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) g)
      have hrest : p (a⁻¹ * g) := ih (fun ρ hρ k hk => hat ρ (Finset.mem_insert_of_mem hρ) k hk)
        _ (mul_mem (inv_mem ha) hg) fun ρ hρ => by
          by_cases e : ρ = τ
          · rw [e, hs]
          · rw [ho ρ e]
            exact hg1 ρ fun h => (Finset.mem_insert.1 h).elim e hρ
      have h := hmul _ _ (hat τ (Finset.mem_insert_self τ A) _
        (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ)) hrest
      rwa [mul_inv_cancel_left] at h

  have vacfact : ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
      IsWeilDatumO ψ V W χS χT ω → ∀ (A : Finset D.what₂.Tau) (Pt : D.what₂.Tau → LPol W.rank V.rank), (∀ τ ∉ A, Pt τ = 1) →
      ∀ x, IsThetaFunO ψ V W x → (∀ τ, vac τ x) → ∀ τ ∉ A, vac τ (GlobalTheory.Chain.ptOf ψ θ M M' x (GlobalTheory.Chain.RealIt.glue Pt)) := by
    intro χS χT ω hW A
    have hψ := hW.std
    have comm := GlobalTheory.T.fockOperators_distinct_real_places_commute_theta D V W S S' M M' θ ψ χS χT ω hθ hW
    dsimp only at comm
    induction A using Finset.induction_on with
    | empty =>
      intro Pt hP x hx vx τ _
      rw [ptOf_glue_one Pt fun τ => hP τ (Finset.notMem_empty τ)]
      exact vx τ
    | insert τ A hτ ih =>
      intro Pt hP x hx vx τ'' h''
      have hP' : ∀ τ' ∉ A, Function.update Pt τ 1 τ' = 1 := fun τ' h => by
        by_cases e : τ' = τ
        · subst e; exact Function.update_self _ _ _
        · rw [Function.update_of_ne e]; exact hP τ' fun h' => (Finset.mem_insert.1 h').elim e h
      have hG := ptOf_theta hψ hx (GlobalTheory.Chain.RealIt.glue (Function.update Pt τ 1))
      rw [ptOf_glue hψ hx Pt τ]
      have hne : τ'' ≠ τ := fun e => h'' (e ▸ Finset.mem_insert_self _ _)
      exact (comm τ'' τ hne _ hG).2.1 (Pt τ) (ih _ hP' x hx vx τ'' fun h => h'' (Finset.mem_insert_of_mem h))
  have key : ∀ (A : Finset D.what₂.Tau) (Pt Qt : D.what₂.Tau → LPol W.rank V.rank), (∀ τ ∉ A, Pt τ = 1) → (∀ τ ∉ A, Qt τ = 1) →
      ∀ g ∈ GinfC V, (∀ τ ∉ A, Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g = 1) →
      ∃ C : ℂ, ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
        IsWeilDatumO ψ V W χS χT ω → (∀ τ, HasInfExp D χT τ (aT τ)) →
        ∀ x y : WO V W → ℂ, IsThetaFunO ψ V W x → (∀ τ, vac τ x) → IsThetaFunO ψ V W y → (∀ τ, vac τ y) →
        GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (GlobalTheory.Chain.ptOf ψ θ M M' x (GlobalTheory.Chain.RealIt.glue Pt)))
          (GlobalTheory.Chain.ptOf ψ θ M M' y (GlobalTheory.Chain.RealIt.glue Qt)) = C * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X x y := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro Pt Qt hP hQ g hg hg1
      refine ⟨1, fun χS χT ω hW hE x y hx vx hy vy => ?_⟩
      have hf := (GlobalTheory.SmoothForms.RealPts.glue θ hθ V).1 g fun τ => hg1 τ (Finset.notMem_empty τ)
      have hg_eq := GlobalTheory.PointAtPlace.eq_one_of_mem V g hf hg
      rw [ptOf_glue_one Pt fun τ => hP τ (Finset.notMem_empty τ),
        ptOf_glue_one Qt fun τ => hQ τ (Finset.notMem_empty τ), hg_eq, ← Prod.one_eq_mk, map_one,
        one_mul]
      rfl
    | insert τ A hτ ih =>
      intro Pt Qt hP hQ g hg hg1
      have upd : ∀ R : D.what₂.Tau → LPol W.rank V.rank, (∀ τ' ∉ insert τ A, R τ' = 1) →
          ∀ τ' ∉ A, Function.update R τ 1 τ' = 1 := fun R hR τ' h => by
        by_cases e : τ' = τ
        · subst e; exact Function.update_self _ _ _
        · rw [Function.update_of_ne e]; exact hR τ' fun h' => (Finset.mem_insert.1 h').elim e h
      obtain ⟨pa, pe1, pe2⟩ := peel g τ
      have hu := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
      set a := atTau θ V τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g) with ha_def
      have hg' : a⁻¹ * g ∈ GinfC V := mul_mem (inv_mem pa) hg
      have hg'1 : ∀ τ' ∉ A, Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ') (a⁻¹ * g) = 1 := fun τ' h => by
        by_cases e : τ' = τ
        · rw [e, pe1]
        · rw [pe2 τ' e]; exact hg1 τ' fun h' => (Finset.mem_insert.1 h').elim e h
      obtain ⟨C', hC'⟩ := ih (Function.update Pt τ 1) (Function.update Qt τ 1) (upd Pt hP) (upd Qt hQ) _ hg' hg'1
      obtain ⟨K, hK⟩ := uniform_place D V W S S' M M' θ ψ hθ m X hX τ (aT τ) _ hu (Pt τ) (Qt τ)
      refine ⟨K * C', fun χS χT ω hW hE x y hx vx hy vy => ?_⟩
      have hψ := hW.std
      have comm := GlobalTheory.T.fockOperators_distinct_real_places_commute_theta D V W S S' M M' θ ψ χS χT ω hθ hW
      dsimp only at comm
      have pmov : ∀ h ∈ GinfC V, (∀ τ' ∉ A, Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ') h = 1) →
          ∀ F, IsThetaFunO ψ V W F → (vac τ F → vac τ (ω (h, 1) F)) ∧ ∀ Q, ω (h, 1) (pt τ F Q) = pt τ (ω (h, 1) F) Q := by
        refine ginf_induction _ ?_ ?_ A ?_
        · intro F _
          rw [← Prod.one_eq_mk, map_one]
          exact ⟨fun h => h, fun _ => rfl⟩
        · intro a b ha hb F hF
          have e : ω (a * b, 1) = ω (a, 1) * ω (b, 1) := by rw [← map_mul, Prod.mk_mul_mk, one_mul]
          have hbF := hW.om_pres (b, 1) F hF
          refine ⟨fun h => ?_, fun Q => ?_⟩
          · rw [e, mul_apply_eq_comp]; exact (ha _ hbF).1 ((hb F hF).1 h)
          · rw [e, mul_apply_eq_comp, (hb F hF).2 Q, (ha _ hbF).2 Q, mul_apply_eq_comp]
        · intro τ' h' k hk F hF
          have hne : τ ≠ τ' := fun e => hτ (e ▸ h')
          exact (comm τ τ' hne F hF).2.2.2 k hk
      have hGx := ptOf_theta hψ hx (GlobalTheory.Chain.RealIt.glue (Function.update Pt τ 1))
      have hGy := ptOf_theta hψ hy (GlobalTheory.Chain.RealIt.glue (Function.update Qt τ 1))
      have vGx := vacfact χS χT ω hW A _ (upd Pt hP) x hx vx τ hτ
      have vGy := vacfact χS χT ω hW A _ (upd Qt hQ) y hy vy τ hτ
      have eg : ω (g, 1) = ω (a, 1) * ω (a⁻¹ * g, 1) := by
        rw [← map_mul, Prod.mk_mul_mk, one_mul, mul_inv_cancel_left]
      obtain ⟨mv, mc⟩ := pmov _ hg' hg'1 _ hGx
      have hF := hW.om_pres (a⁻¹ * g, 1) _ hGx
      rw [ptOf_glue hψ hx Pt τ, ptOf_glue hψ hy Qt τ, eg,
        mul_apply_eq_comp, mc (Pt τ)]
      rw [hK χS χT ω hW (hE τ) _ _ hF (mv vGx) hGy vGy, hC' χS χT ω hW hE x y hx vx hy vy]
      ring
  intro Pt Qt g hg
  exact key Finset.univ Pt Qt (fun τ h => (h (Finset.mem_univ τ)).elim) (fun τ h => (h (Finset.mem_univ τ)).elim) g hg
    fun τ h => (h (Finset.mem_univ τ)).elim

section Lin
variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D)
  (ψ : AddChar (AF D.host.F) ℂ)

theorem ptOf_add' (x : WO V W → ℂ) (P P' : PolF D W.rank V.rank) :
    GlobalTheory.Chain.ptOf ψ θ M M' x (P + P') = GlobalTheory.Chain.ptOf ψ θ M M' x P + GlobalTheory.Chain.ptOf ψ θ M M' x P' := by
  unfold GlobalTheory.Chain.ptOf; exact map_add _ _ _

theorem ptOf_smul' (x : WO V W → ℂ) (c : ℂ) (P : PolF D W.rank V.rank) :
    GlobalTheory.Chain.ptOf ψ θ M M' x (c • P) = c • GlobalTheory.Chain.ptOf ψ θ M M' x P := by
  unfold GlobalTheory.Chain.ptOf; exact map_smul _ _ _

theorem ptOf_zero' (x : WO V W → ℂ) : GlobalTheory.Chain.ptOf ψ θ M M' x (0 : PolF D W.rank V.rank) = 0 := by
  unfold GlobalTheory.Chain.ptOf; exact map_zero _

end Lin

theorem uniform_all : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ∀ (m : Measure (WO V W)) (X : Set (WO V W)), IsCovolOne (ratL W V) m X → ∀ (aT : D.what₂.Tau → ℚ) (P Q : PolF D W.rank V.rank), ∀ g ∈ GinfC V, ∃ C : ℂ, ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → (∀ τ, HasInfExp D χT τ (aT τ)) → ∀ x y : WO V W → ℂ, IsThetaFunO ψ V W x → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) x) → IsThetaFunO ψ V W y → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) y) → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (GlobalTheory.Chain.ptOf ψ θ M M' x P)) (GlobalTheory.Chain.ptOf ψ θ M M' y Q) = C * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X x y := by
  intro D V W S S' M M' θ ψ hθ m X hX aT P Q g hg
  obtain ⟨hμ, h𝓕, -⟩ := id hX
  have ptOf_theta (hψ : IsStdChar D ψ (-1)) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
      (P : PolF D W.rank V.rank) : IsThetaFunO ψ V W (GlobalTheory.Chain.ptOf ψ θ M M' f P) :=
    GlobalTheory.FockIndep.pure_mem
      (A := aPlusAll (heisO ψ V W) θ (fun τ => cplxO (cart M τ) (cart M' τ)) (onb M) (onb M'))
      (fun _ _ => GlobalTheory.WeilVacMove.isTheta_add)
      (fun c _ => GlobalTheory.WeilVacMove.isTheta_smul c)
      (fun i _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ i.1 _ _ h) hf P
  let Good : PolF D W.rank V.rank → PolF D W.rank V.rank → Prop := fun P Q => ∃ C : ℂ, ∀ (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → (∀ τ, HasInfExp D χT τ (aT τ)) →
    ∀ x y : WO V W → ℂ, IsThetaFunO ψ V W x → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) x) →
      IsThetaFunO ψ V W y → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) y) →
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (GlobalTheory.Chain.ptOf ψ θ M M' x P)) (GlobalTheory.Chain.ptOf ψ θ M M' y Q) =
        C * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X x y
  have hspan : ∀ R : PolF D W.rank V.rank, R ∈ Submodule.span ℂ (Set.range
      (GlobalTheory.Chain.RealIt.glue : (D.what₂.Tau → LPol W.rank V.rank) → PolF D W.rank V.rank)) := fun R => by
    rw [GlobalTheory.Chain.RealIt.GlueProof.glue_span]; exact Submodule.mem_top

  have stepP : ∀ Q', (∀ Pt : D.what₂.Tau → LPol W.rank V.rank, Good (GlobalTheory.Chain.RealIt.glue Pt) Q') → ∀ P', Good P' Q' := by
    intro Q' hQ' P'
    induction hspan P' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨Pt, rfl⟩ := hz
      exact hQ' Pt
    | zero =>
      refine ⟨0, fun χS χT ω hW hE x y hx vx hy vy => ?_⟩
      rw [ptOf_zero', map_zero, zero_mul]
      simp [GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh]
    | add z z' _ _ hz hz' =>
      obtain ⟨C₁, h₁⟩ := hz
      obtain ⟨C₂, h₂⟩ := hz'
      refine ⟨C₁ + C₂, fun χS χT ω hW hE x y hx vx hy vy => ?_⟩
      have hψ := hW.std
      rw [ptOf_add', map_add (f := _), GlobalTheory.ThetaL2InnerProduct.ipTh_eq,
        GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 (hW.om_pres _ _ (ptOf_theta hψ hx z))
          (hW.om_pres _ _ (ptOf_theta hψ hx z')) (ptOf_theta hψ hy Q'),
        ← GlobalTheory.ThetaL2InnerProduct.ipTh_eq, ← GlobalTheory.ThetaL2InnerProduct.ipTh_eq, h₁ χS χT ω hW hE x y hx vx hy vy,
        h₂ χS χT ω hW hE x y hx vx hy vy]
      ring
    | smul c z _ hz =>
      obtain ⟨C₁, h₁⟩ := hz
      refine ⟨c * C₁, fun χS χT ω hW hE x y hx vx hy vy => ?_⟩
      rw [ptOf_smul', map_smul, GlobalTheory.ThetaL2InnerProduct.ipTh_eq, GlobalTheory.Size.ipO_smul_left, ← GlobalTheory.ThetaL2InnerProduct.ipTh_eq,
        h₁ χS χT ω hW hE x y hx vx hy vy]
      ring
  have stepQ : ∀ P', (∀ Qt : D.what₂.Tau → LPol W.rank V.rank, Good P' (GlobalTheory.Chain.RealIt.glue Qt)) → ∀ Q', Good P' Q' := by
    intro P' hP' Q'
    induction hspan Q' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨Qt, rfl⟩ := hz
      exact hP' Qt
    | zero =>
      refine ⟨0, fun χS χT ω hW hE x y hx vx hy vy => ?_⟩
      rw [ptOf_zero', zero_mul]
      simp [GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh]
    | add z z' _ _ hz hz' =>
      obtain ⟨C₁, h₁⟩ := hz
      obtain ⟨C₂, h₂⟩ := hz'
      refine ⟨C₁ + C₂, fun χS χT ω hW hE x y hx vx hy vy => ?_⟩
      have hψ := hW.std
      rw [ptOf_add', GlobalTheory.ThetaL2InnerProduct.ipTh_eq,
        GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 (hW.om_pres _ _ (ptOf_theta hψ hx P'))
          (ptOf_theta hψ hy z) (ptOf_theta hψ hy z'),
        ← GlobalTheory.ThetaL2InnerProduct.ipTh_eq, ← GlobalTheory.ThetaL2InnerProduct.ipTh_eq, h₁ χS χT ω hW hE x y hx vx hy vy,
        h₂ χS χT ω hW hE x y hx vx hy vy]
      ring
    | smul c z _ hz =>
      obtain ⟨C₁, h₁⟩ := hz
      refine ⟨starRingEnd ℂ c * C₁, fun χS χT ω hW hE x y hx vx hy vy => ?_⟩
      rw [ptOf_smul', GlobalTheory.ThetaL2InnerProduct.ipTh_eq, GlobalTheory.Size.ipO_smul_right, ← GlobalTheory.ThetaL2InnerProduct.ipTh_eq,
        h₁ χS χT ω hW hE x y hx vx hy vy]
      ring
  have hglue : ∀ Pt Qt : D.what₂.Tau → LPol W.rank V.rank, Good (GlobalTheory.Chain.RealIt.glue Pt) (GlobalTheory.Chain.RealIt.glue Qt) :=
    fun Pt Qt => uniform_glue D V W S S' M M' θ ψ hθ m X hX aT Pt Qt g hg
  exact stepQ P (fun Qt => stepP _ (fun Pt => hglue Pt Qt) P) Q

theorem coef_indep_exponents : ∀ (D : D7) (k : Fin D.R.m) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω ω' : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f f' : WO V W → ℂ), IsInfFam θ → IsWeilExp ψ V W (GlobalTheory.Chain.expS D k) (GlobalTheory.Chain.expT D k) ω → IsWeilExp ψ V W (GlobalTheory.Chain.expS D k) (GlobalTheory.Chain.expT D k) ω' → GlobalTheory.Chain.IsVacVec ψ θ M M' f → GlobalTheory.Chain.IsVacVec ψ θ M M' f' → ∀ m X, IsCovolOne (ratL W V) m X → ∀ P, ∀ g ∈ GinfC V, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (GlobalTheory.Chain.ptOf ψ θ M M' f P)) (GlobalTheory.Chain.ptOf ψ θ M M' f P) * (nrm2 m X f' : ℂ) = GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω' (g, 1) (GlobalTheory.Chain.ptOf ψ θ M M' f' P)) (GlobalTheory.Chain.ptOf ψ θ M M' f' P) * (nrm2 m X f : ℂ) := by
  intro D k V W S S' M M' θ ψ ω ω' f f' hθ hω hω' hf hf' m X hX P g hg
  obtain ⟨χS, χT, hW, hE⟩ := hω
  obtain ⟨χS', χT', hW', hE'⟩ := hω'
  obtain ⟨C, hC⟩ := uniform_all D V W S S' M M' θ ψ hθ m X hX (GlobalTheory.Chain.expT D k) P P g hg
  have e1 := hC χS χT ω hW (fun τ => (hE τ).2) f f hf.theta hf.vac hf.theta hf.vac
  have e2 := hC χS' χT' ω' hW' (fun τ => (hE' τ).2) f' f' hf'.theta hf'.vac hf'.theta hf'.vac
  have nr : ∀ h : WO V W → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X h h = ((nrm2 m X h : ℝ) : ℂ) := by
    intro h
    unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh nrm2
    rw [← integral_complex_ofReal]
    congr 1
    funext w
    show h w * (starRingEnd ℂ) (h w) = _
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [e1, e2, ← nr, ← nr]
  ring

end GlobalTheory.FockCoefIndep
