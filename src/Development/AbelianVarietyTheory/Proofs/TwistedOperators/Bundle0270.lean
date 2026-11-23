module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0258
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometryConjDifferByInnerAutomorphism
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InnerTwist

theorem exists_inv {R : Type} [CommRing R] {m n : ℕ} (j : Matrix (Fin m) (Fin n) R)
    (h : Function.Bijective j.mulVec) : ∃ j' : Matrix (Fin n) (Fin m) R, j * j' = 1 ∧ j' * j = 1 := by
  let e := LinearEquiv.ofBijective (Matrix.mulVecLin j) h
  refine ⟨LinearMap.toMatrix' (e.symm : (Fin m → R) →ₗ[R] (Fin n → R)), ?_, ?_⟩
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun x => ?_
    exact e.apply_symm_apply x
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun x => ?_
    exact e.symm_apply_apply x

variable {D : D7}

theorem mat_ext {k l : Type} (X Y : Matrix k l (AF D.host.F ⊗[D.host.F] D.host.E))
    (h1 : X.map (GlobalTheory.FinIsoGrp.pInf D) = Y.map (GlobalTheory.FinIsoGrp.pInf D))
    (h2 : X.map (GlobalTheory.FinIsoGrp.qFin D) = Y.map (GlobalTheory.FinIsoGrp.qFin D)) : X = Y := by
  ext i i'
  exact GlobalTheory.FinIsoGrp.proj_inj D _ _ (congrFun (congrFun h1 i) i') (congrFun (congrFun h2 i) i')

theorem infHom_val (V : HSp D) (g : GA D V) :
    (infHom V g).val = (matHom V g).val.map (GlobalTheory.FinIsoGrp.pInf D) := by
  refine Matrix.ext fun i k => ?_
  rfl

theorem gfc_ext (V : HSp D) (x y : GfC V)
    (h : (finE V (x : GA D V)).val = (finE V (y : GA D V)).val) : x = y := by
  have hx : infHom V (x : GA D V) = 1 := x.2
  have hy : infHom V (y : GA D V) = 1 := y.2
  have hm : (matHom V (x : GA D V)).val = (matHom V (y : GA D V)).val := by
    apply mat_ext
    · rw [← infHom_val, ← infHom_val, hx, hy]
    · rw [← GlobalTheory.FinIsoGrp.finE_val, ← GlobalTheory.FinIsoGrp.finE_val, h]
  have inj : Function.Injective (matHom V) := Subgroup.subtype_injective _
  exact Subtype.ext (inj (Units.ext hm))

end GlobalTheory.InnerTwist

namespace GlobalTheory.InnerTwist

variable {D : D7}

theorem map_one' {R S : Type} [CommRing R] [CommRing S] {n : Type} [Fintype n] [DecidableEq n] (f : R →+* S) :
    (1 : Matrix n n R).map f = 1 :=
  Matrix.map_one _ (RingHom.map_zero f) (RingHom.map_one f)

theorem lift_abs {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] {n : Type} [Fintype n] [DecidableEq n]
    (σ : R →+* R) (σ₁ : R₁ →+* R₁) (σ₂ : R₂ →+* R₂) (p : R →+* R₁) (q : R →+* R₂)
    (hinj : ∀ x y, p x = p y → q x = q y → x = y) (s : R₂ → R) (hs1 : ∀ y, p (s y) = 0) (hs2 : ∀ y, q (s y) = y)
    (hp : ∀ x, p (σ x) = σ₁ (p x)) (hq : ∀ x, q (σ x) = σ₂ (q x)) (J : Matrix n n R) (X Y : Matrix n n R₂)
    (hXY : X * Y = 1) (hYX : Y * X = 1) (hX : Formalism.UG.cT σ₂ X * J.map q * X = J.map q) :
    ∃ u : GL n R, Formalism.UG.cT σ (u : Matrix n n R) * J * (u : Matrix n n R) = J ∧
      (u : Matrix n n R).map p = 1 ∧ (u : Matrix n n R).map q = X := by
  have ext : ∀ {k l : Type} (A B : Matrix k l R), A.map p = B.map p → A.map q = B.map q → A = B := by
    intro k l A B ha hb
    ext i i'
    exact hinj _ _ (congrFun (congrFun ha i) i') (congrFun (congrFun hb i) i')
  let lift : Matrix n n R₂ → Matrix n n R := fun Z => (1 - s 1) • (1 : Matrix n n R) + Z.map s
  have lp : ∀ Z, (lift Z).map p = 1 := by
    intro Z; ext i k
    by_cases h : i = k <;> simp [lift, Matrix.one_apply, h, hs1]
  have lq : ∀ Z, (lift Z).map q = Z := by
    intro Z; ext i k
    by_cases h : i = k <;> simp [lift, Matrix.one_apply, h, hs2]
  have hmul : ∀ Z W : Matrix n n R₂, Z * W = 1 → lift Z * lift W = 1 := by
    intro Z W hZW
    apply ext
    · rw [Matrix.map_mul, lp, lp, Matrix.one_mul, map_one']
    · rw [Matrix.map_mul, lq, lq, hZW, map_one']
  have cp : ∀ A : Matrix n n R, (Formalism.UG.cT σ A).map p = Formalism.UG.cT σ₁ (A.map p) := by
    intro A; ext i k; exact hp _
  have cq : ∀ A : Matrix n n R, (Formalism.UG.cT σ A).map q = Formalism.UG.cT σ₂ (A.map q) := by
    intro A; ext i k; exact hq _
  refine ⟨⟨lift X, lift Y, hmul X Y hXY, hmul Y X hYX⟩, ?_, lp X, lq X⟩
  show Formalism.UG.cT σ (lift X) * J * lift X = J
  apply ext
  · rw [Matrix.map_mul, Matrix.map_mul, cp, lp, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, cq, lq]
    exact hX

theorem exists_fin (V : HSp D) (X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (hXY : X * Y = 1) (hYX : Y * X = 1)
    (hX : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) X *
        V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * X =
      V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) :
    ∃ b : GfC V, (finE V (b : GA D V)).val = X := by
  choose s hs1 hs2 using GlobalTheory.FinIsoGrp.proj_surj D
  rw [← GlobalTheory.FinIsoGrp.gram_map] at hX
  obtain ⟨u, hu, hup, huq⟩ := lift_abs (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig)
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf D.host.F) D.sp.cm.sig) (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (GlobalTheory.FinIsoGrp.pInf D) (GlobalTheory.FinIsoGrp.qFin D) (GlobalTheory.FinIsoGrp.proj_inj D) s hs1 hs2
    (fun x => GlobalTheory.FinIsoGrp.map_sig (fstA D.host.F) D.sp.cm.sig x) (GlobalTheory.FinIsoGrp.qFin_sig D)
    (JR (AF D.host.F) V.gram) X Y hXY hYX hX
  let b0 : GA D V := (⟨u, hu⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)
  have hb : infHom V b0 = 1 := by
    apply Units.ext
    exact (infHom_val V b0).trans hup
  refine ⟨⟨b0, hb⟩, ?_⟩
  rw [GlobalTheory.FinIsoGrp.finE_val]
  exact huq

theorem alg {R : Type} [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (σ : R →+* R) (j j₀ : Matrix m n R) (j' k' : Matrix n m R) (G : Matrix n n R) (G' : Matrix m m R)
    (h1 : j * j' = 1) (h2 : j' * j = 1) (k1 : j₀ * k' = 1) (k2 : k' * j₀ = 1)
    (hJ : Formalism.UG.cT σ j * G' * j = G) (hJ₀ : Formalism.UG.cT σ j₀ * G' * j₀ = G) :
    Formalism.UG.cT σ (k' * j) * G * (k' * j) = G ∧ (k' * j) * (j' * j₀) = 1 ∧ (j' * j₀) * (k' * j) = 1 := by
  have hk : Formalism.UG.cT σ k' * G * k' = G' := by
    calc Formalism.UG.cT σ k' * G * k' = Formalism.UG.cT σ (j₀ * k') * G' * (j₀ * k') := by
          rw [← hJ₀, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = G' := by rw [k1, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · calc Formalism.UG.cT σ (k' * j) * G * (k' * j) = Formalism.UG.cT σ j * (Formalism.UG.cT σ k' * G * k') * j := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hk, hJ]
  · calc (k' * j) * (j' * j₀) = k' * (j * j') * j₀ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, k2]
  · calc (j' * j₀) * (k' * j) = j' * (j₀ * k') * j := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [k1, Matrix.mul_one, h2]

theorem alg2 {R : Type} [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (j j₀ : Matrix m n R) (j' k' : Matrix n m R) (h1 : j * j' = 1) (k1 : j₀ * k' = 1)
    (P Q : Matrix m m R) (A : Matrix n n R) (c1 : P * j = j * A) (c2 : Q * j₀ = j₀ * ((k' * j) * A * (j' * j₀))) :
    P = Q := by
  have e1 : P = j * A * j' := by
    calc P = P * (j * j') := by rw [h1, Matrix.mul_one]
      _ = j * A * j' := by rw [← Matrix.mul_assoc, c1]
  have e2 : Q = j * A * j' := by
    calc Q = Q * (j₀ * k') := by rw [k1, Matrix.mul_one]
      _ = (j₀ * k') * j * A * j' * (j₀ * k') := by
          rw [← Matrix.mul_assoc, c2]; simp only [Matrix.mul_assoc]
      _ = j * A * j' := by rw [k1, Matrix.one_mul, Matrix.mul_one]
  rw [e1, e2]

theorem inv_val {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (u : GL n R) (X Y : Matrix n n R)
    (hu : u.val = X) (hYX : Y * X = 1) : (u⁻¹).val = Y := by
  calc (u⁻¹).val = (Y * X) * (u⁻¹).val := by rw [hYX, Matrix.one_mul]
    _ = Y * (u.val * (u⁻¹).val) := by rw [hu]; simp only [Matrix.mul_assoc]
    _ = Y := by rw [Units.mul_inv, Matrix.mul_one]

theorem conj_inner : ∀ (D : D7) (V V' : HSp D) (j j₀ : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Φ Φ₀ : GfC V ≃ₜ* GfC V'), GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsIsom V V' (Formalism.L2.Herm.Af D.host.F) j → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsIsom V V' (Formalism.L2.Herm.Af D.host.F) j₀ → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsConjBy V V' j Φ → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsConjBy V V' j₀ Φ₀ → ∃ b : GfC V, ∀ g, Φ g = Φ₀ (b * g * b⁻¹) := by
  intro D V V' j j₀ Φ Φ₀ hj hj₀ hΦ hΦ₀
  obtain ⟨j', h1, h2⟩ := exists_inv j hj.1
  obtain ⟨k', k1, k2⟩ := exists_inv j₀ hj₀.1
  obtain ⟨hX, hXY, hYX⟩ := alg _ j j₀ j' k' _ _ h1 h2 k1 k2 hj.2 hj₀.2
  obtain ⟨b, hb⟩ := exists_fin V _ _ hXY hYX hX
  refine ⟨b, fun g => gfc_ext V' _ _ ?_⟩
  have hbinv := inv_val (finE V (b : GA D V)) _ _ hb hYX
  have e0 : (finE V ((b * g * b⁻¹ : GfC V) : GA D V)).val =
      HMul.hMul (HMul.hMul (HMul.hMul k' j) (finE V (g : GA D V)).val) (HMul.hMul j' j₀) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
      hbinv, hb]
  have c2 := hΦ₀ (b * g * b⁻¹)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.mmul at c2
  rw [e0] at c2
  exact alg2 j j₀ j' k' h1 k1 _ _ _ (hΦ g) c2

end GlobalTheory.InnerTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLiftDatumOfConjugateLiftDatumStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLiftDatum_of_conjugate_liftDatum : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ μ' η', ChiAt R i σ μ' → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∀ ω f₀ f B io thP, GlobalTheory.GalLift.LiftData R i σ μ' η' c H ω f₀ f B io thP → ∃ s m, GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io ∧ IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) ∧ Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y ∧ H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) := by
  first | exact @GlobalTheory.ConjLiftData.isLiftDataC_of_liftData | exact GlobalTheory.ConjLiftData.isLiftDataC_of_liftData | (intros; apply GlobalTheory.ConjLiftData.isLiftDataC_of_liftData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardWeightSetGridEqGridRowSpaceRank
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.Grid

theorem card_weightX_grid : ∀ (D : D7), HostHyp D → ∀ (τ : D.what₂.Tau) (j : ℕ), 1 ≤ j → j ≤ D.R.m →
    ((GlobalTheory.Grid.grid D τ).weightX j).card = GlobalTheory.Grid.rkX D j := by
  intro D _ τ j _ hj
  have hcen : GlobalTheory.Grid.cen D τ = GlobalTheory.ChiGrid.cen D 1 τ := by
    funext i
    unfold GlobalTheory.Grid.cen GlobalTheory.ChiGrid.cen GlobalTheory.Grid.gridOf
    rw [GlobalTheory.GridJoin.gap_eq_chiGap D]
    rfl
  have hg : GlobalTheory.Grid.grid D τ = GlobalTheory.ChiGrid.num D 1 τ := by
    unfold GlobalTheory.Grid.grid GlobalTheory.Grid.gridOf GlobalTheory.ChiGrid.num
    rw [hcen, GlobalTheory.GridJoin.gap_eq_chiGap D]
    rfl
  rw [hg]
  let Γ := GlobalTheory.ChiGrid.num D 1 τ
  have num_e {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : (((Γ).e l : ℤ) : ℚ) = (D.hc τ).e ⟨l - 1, by omega⟩ := by
    obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    exact GlobalTheory.SignedHC.GridData.extend_cast 1 (D.hc τ).e_int ⟨l, by omega⟩
  
  have num_b {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : (((Γ).b l : ℤ) : ℚ) = (D.hc τ).b ⟨l - 1, by omega⟩ := by
    obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    exact GlobalTheory.SignedHC.GridData.extend_cast 1 (D.hc τ).b_int ⟨l, by omega⟩
  
  have num_v {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : (((Γ).v i : ℤ) : ℚ) = (D.hc τ).v ⟨i - 2, by omega⟩ := by
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
    exact GlobalTheory.SignedHC.GridData.extend_cast 2 (D.hc τ).v_int ⟨i, by omega⟩
  
  have num_be {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : ((D.R.t : ℚ) + 3) / 2 ≤ ((Γ).e l : ℚ) - (Γ).b l := by
    rw [num_e h1 h2, num_b h1 h2]
    exact (D.hc τ).gap_be _
  
  have num_eb {l : ℕ} (h1 : 1 ≤ l) (h2 : l + 1 ≤ D.R.m) : ((D.R.t : ℚ) + 3) / 2 ≤ ((Γ).b (l + 1) : ℚ) - (Γ).e l := by
    rw [num_e h1 (by omega), num_b (by omega) h2]
    obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    exact (D.hc τ).gap_eb ⟨l, by omega⟩ (by simpa using (by omega : l + 1 < D.R.m))
  
  have num_e_lt {l l' : ℕ} (h1 : 1 ≤ l) (h : l < l') (h2 : l' ≤ D.R.m) : (D.R.t : ℚ) + 3 + (Γ).e l ≤ (Γ).e l' := by
    induction l', h using Nat.le_induction with
    | base =>
      linarith [num_be (l := l + 1) (by omega) h2, num_eb h1 h2]
    | succ n hn ih =>
      have := ih (by omega)
      have e1 := num_be (l := n + 1) (by omega) h2
      have e2 := num_eb (l := n) (by omega) h2
      have : (0 : ℚ) ≤ D.R.t := by positivity
      linarith
  
  have num_cloud {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : -((Γ).b 1 : ℚ) + 1 ≤ (Γ).v i := by
    have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    have hk : 2 ≤ D.R.k := by omega
    have base : -((Γ).b 1 : ℚ) < (Γ).v D.R.k := by
      rw [num_v hk le_rfl, num_b le_rfl hm]
      have e1 := (D.hc τ).u_last_gt (by omega) (by omega)
      have e2 := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
      have e3 : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext (by simp only; omega)
      simp only [e3] at e2
      exact e1.trans e2
    have base' : -((Γ).b 1) < (Γ).v D.R.k := by exact_mod_cast base
    have step : (Γ).v D.R.k ≤ (Γ).v i := by
      rcases h2.eq_or_lt with rfl | h
      · exact le_rfl
      · exact ((Γ).v_anti i D.R.k h1 h le_rfl).le
    have : -((Γ).b 1) + 1 ≤ (Γ).v i := by omega
    exact_mod_cast this
  
  have a_le {i j : ℕ} (h : i ≤ j) : (Γ).a j ≤ (Γ).a i := by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · have : (0 : ℚ) ≤ (Γ).ga := by positivity
      linarith [GlobalTheory.ChiGrid.a_add_le (G := Γ) h]
  
  have hblock {l : ℕ} {x : ℚ} (h : x ∈ (GlobalTheory.ChiGrid.num D 1 τ).blockMPlus l) :
      -((GlobalTheory.ChiGrid.num D 1 τ).e l : ℚ) - (D.R.t : ℚ) / 2 ≤ x ∧ x ≤ -((GlobalTheory.ChiGrid.num D 1 τ).e l : ℚ) + (D.R.t : ℚ) / 2 := by
    have h' := abs_le.1 (GlobalTheory.SignedHC.abs_sub_le_of_mem_block h)
    have e : (((GlobalTheory.ChiGrid.num D 1 τ).t + 1 : ℕ) : ℚ) = D.R.t + 1 := by push_cast; rfl
    rw [e] at h'
    constructor <;> linarith [h'.1, h'.2]
  have habove {j : ℕ} (hj : j + 1 ≤ D.R.m) {x y : ℚ} (hx : x ∈ (GlobalTheory.ChiGrid.num D 1 τ).weightX j) (hy : y ∈ (GlobalTheory.ChiGrid.num D 1 τ).blockMPlus (j + 1)) : y < x := by
    let Γ := GlobalTheory.ChiGrid.num D 1 τ
    have hm : 1 ≤ D.R.m := by omega
    have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    have ht : (0 : ℚ) ≤ D.R.t := by positivity
    have hg : (0 : ℚ) ≤ Γ.ga := by positivity
    obtain ⟨y1, y2⟩ := hblock hy
    have hbe := num_be (l := 1) le_rfl hm
    have he1 : ((Γ.e 1 : ℚ)) ≤ Γ.e (j + 1) := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · exact le_rfl
      · linarith [num_e_lt (l := 1) (l' := j + 1) le_rfl (by omega) hj]
    have hlow : y < -(Γ.b 1 : ℚ) := by linarith
    have hc2 := num_cloud (i := 2) le_rfl hk
    have ham : Γ.a Γ.m = Γ.v 2 + Γ.ga + 1 / 2 := Γ.a_m
    rcases GlobalTheory.SignedHC.GridData.mem_weightX.1 hx with h | h | ⟨i, h1, h2, h⟩ | ⟨l, h1, h2, h⟩
    · obtain ⟨i, hi, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_tops.1 h
      linarith [a_le hi]
    · obtain ⟨i, h1, h2, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h
      have := num_cloud h1 h2
      simp only [GlobalTheory.SignedHC.GridData.vHalf]
      linarith
    · have := (GlobalTheory.ChiGrid.blockC'_between (GlobalTheory.ChiGrid.num_nearMid D 1 τ) (GlobalTheory.ChiGrid.odd_sLen D).pos (GlobalTheory.ChiGrid.sLen_lt_gap D 1) h1 h2 h).1
      linarith [a_le h2]
    · have := num_e_lt h1 (by omega : l < j + 1) hj
      have := (hblock h).1
      linarith
  have hcard : ∀ {j : ℕ}, j ≤ D.R.m → ((GlobalTheory.ChiGrid.num D 1 τ).weightX j).card = GlobalTheory.ChiGrid.rankX D j := by
    intro j hj
    induction j with
    | zero =>
      rw [GlobalTheory.ChiGrid.card_weightX_zero (GlobalTheory.ChiGrid.num_nearMid D 1 τ) (GlobalTheory.ChiGrid.odd_sLen D).pos (GlobalTheory.ChiGrid.sLen_lt_gap D 1)]
      simp [GlobalTheory.ChiGrid.rankX]; rfl
    | succ j ih =>
      rw [(GlobalTheory.ChiGrid.num D 1 τ).weightX_succ, Finset.card_union_of_disjoint
        (Finset.disjoint_left.2 fun x hx hy => (habove hj hx hy).ne rfl), ih (by omega)]
      have : ((GlobalTheory.ChiGrid.num D 1 τ).blockMPlus (j + 1)).card = D.R.t + 1 := GlobalTheory.SignedHC.card_block _ _
      rw [this]
      simp only [GlobalTheory.ChiGrid.rankX]
      ring
  rw [hcard hj]
  rfl

end GlobalTheory.Grid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasselmanWallachMultMapEquivariantSobolevContinu
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GKExtFields

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem dRep_rep_conj (M : DSModel V S) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (w : M.H τ) :
    dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) w = dRep (M.σ τ) X w := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  unfold Formalism.L2.Theta.dRep DSModel.rep
  congr 1
  funext t
  have h1 : t • ((M.fr τ)⁻¹ * X * M.fr τ) = (M.fr τ)⁻¹ * (t • X) * M.fr τ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [h1, Matrix.exp_conj' _ _ (M.fr_unit τ)]
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

theorem foldr_dRep_conj (M : DSModel V S) (τ : D.what₂.Tau) (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (w : M.H τ) :
    (l.map fun X => (M.fr τ)⁻¹ * X * M.fr τ).foldr (dRep (M.rep τ)) w = l.foldr (dRep (M.σ τ)) w := by
  induction l with
  | nil => rfl
  | cons X l ih => simp only [List.map_cons, List.foldr_cons, ih, dRep_rep_conj]

theorem conj_mem_lieAt (M : DSModel V S) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) : (M.fr τ)⁻¹ * X * M.fr τ ∈ lieAt V τ := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hX' : Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X = 0 := hX
  show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0
  rw [← M.fr_gram τ]
  have h1 : ∀ Z : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, conjTranspose_one, Matrix.one_mul]
  have h2 : ∀ Z : Matrix (Fin V.rank) (Fin V.rank) ℂ, M.fr τ * ((M.fr τ)⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  have h3 : (M.fr τ)ᴴ * (Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X) * M.fr τ = 0 := by
    rw [hX']; simp
  simp only [conjTranspose_mul, Matrix.mul_assoc, h1, h2]
  simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc] using h3

theorem multMap_fields : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (ι : E →ₗ[ℂ] (GA D V → ℂ)) (N : ℕ) (π : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E)), (∀ d x, p d x = (GlobalTheory.Size.growthSob θ V d N (ι x)).toReal) → (∀ x d, GlobalTheory.Size.growthSob θ V d N (ι x) ≠ ⊤) → (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ x, ι (π τ g x) = rTr V ((GlobalTheory.ChainFr.Fr.ofModel M).elt θ τ g) (ι x)) → ∀ T : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) E, (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.σ τ g (v τ) → T (Function.update v τ w) = π τ g (T v)) → (∀ τ (i : ℕ) (v : M.Vec), ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) ∧ ∀ w : M.sm τ, p i (T (Function.update v τ w)) ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → ι (T (Function.update v τ w)) = rTr V (atTau θ V τ g) (ι (T v))) ∧ ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = ι (T (Function.update v τ w)) x := by
  intro D θ V S M E _ _ _ _ _ _ p ι N π hp hfin hπ T hTe hTc
  refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have hg' : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
      GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) hg
    rw [hTe τ _ hg' v w hw, hπ τ _ hg']
    have he : (GlobalTheory.ChainFr.Fr.ofModel M).elt θ τ (M.fr τ * g * (M.fr τ)⁻¹) = atTau θ V τ g := by
      show atTau θ V τ ((M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ) = atTau θ V τ g
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
    rw [he]
  · let f : M.sm τ →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (ι.comp (T.toLinearMap v τ))
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend f
    have hℓw : ∀ w : M.sm τ, ℓ w = ι (T (Function.update v τ w)) x := fun w => by
      have := LinearMap.congr_fun hℓ w
      simpa [f, MultilinearMap.toLinearMap_apply] using this
    refine ⟨ℓ, ?_, hℓw⟩
    obtain ⟨L, C, hL, hC⟩ := hTc τ 0 v
    refine ⟨L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ), GlobalTheory.Grow.height V x ^ N * C, ?_, fun w hw => ?_⟩
    · intro l hl X hX
      obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
      obtain ⟨X₀, hX₀, rfl⟩ := List.mem_map.1 hX
      exact GlobalTheory.GKExtFields.conj_mem_lieAt M τ (hL l₀ hl₀ X₀ hX₀)
    · have hmem : w ∈ M.sm τ := Submodule.subset_span hw
      have hw' : ℓ w = ι (T (Function.update v τ ⟨w, hmem⟩)) x := hℓw ⟨w, hmem⟩
      rw [hw']
      set y := T (Function.update v τ ⟨w, hmem⟩)
      have hpos : 0 < GlobalTheory.Grow.height V x ^ N := pow_pos (GlobalTheory.Grow.height_pos V x) N
      have hsz : p 0 y = (GlobalTheory.Size.growthSize V N (ι y)).toReal := by
        rw [hp]; simp [GlobalTheory.Size.growthSob]
      have hne : GlobalTheory.Size.growthSize V N (ι y) ≠ ⊤ := by
        have := hfin y 0; simpa [GlobalTheory.Size.growthSob] using this
      have hb : ‖ι y x‖ ≤ GlobalTheory.Grow.height V x ^ N * p 0 y := by
        have h1 : ENNReal.ofReal (‖ι y x‖ / GlobalTheory.Grow.height V x ^ N) ≤ GlobalTheory.Size.growthSize V N (ι y) :=
          le_iSup (fun g => ENNReal.ofReal (‖ι y g‖ / GlobalTheory.Grow.height V g ^ N)) x
        rw [ENNReal.ofReal_le_iff_le_toReal hne, div_le_iff₀ hpos, ← hsz] at h1
        linarith
      have hs : ((L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ)).map
          fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum = GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L (⟨w, hmem⟩ : M.sm τ) := by
        unfold GlobalTheory.SmoothGlob.sobNorm
        rw [List.map_map]
        congr 1
        refine List.map_congr_left fun l _ => ?_
        simp only [Function.comp_apply, GlobalTheory.GKExtFields.foldr_dRep_conj]
      rw [hs, mul_assoc]
      exact hb.trans (mul_le_mul_of_nonneg_left (hC ⟨w, hmem⟩) hpos.le)

end GlobalTheory.GKExtFields

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermLocallyIntegrable
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

namespace GlobalTheory.ConstantTermL2

theorem main : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule D.host.E V.V) (hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W) (F : DividedPowerChartLift V μ), LocallyIntegrable (constTerm (.single hW) (lift (GQ V) F)) μ ∧ (∀ u ∈ NA (.single hW), (fun g => constTerm (.single hW) (lift (GQ V) F) (u * g)) =ᵐ[μ] constTerm (.single hW) (lift (GQ V) F)) ∧ ∀ f : GA D V → ℂ, Continuous f → HasCompactSupport f → ∀ x, constTerm (.single hW) (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) x = ∫ y, f (x⁻¹ * y) * constTerm (.single hW) (lift (GQ V) F) y ∂μ := by
  intro D V μ _ _ W hW F
  have hc := cocompact_single hW
  have hl := leftInv_lift (Γ := GQ V) F
  have hm : StronglyMeasurable (lift (GQ V) F) := (Lp.stronglyMeasurable F).comp_measurable measurable_mk
  have hi := GlobalTheory.CuspAE.locallyIntegrable_lift (Γ := GQ V) (μ := μ) F
  refine ⟨GlobalTheory.CuspAE.locallyIntegrable_constTermOn hc hl hm hi, fun u hu => .of_forall fun g =>
    hc.constTermOn_mul_left hl hu g, fun f hf hs x => ?_⟩
  have e1 : (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) = convR μ f (lift (GQ V) F) :=
    funext fun x => (convR_eq (μ := μ) f _ x).symm
  rw [e1, ← convR_eq (μ := μ)]
  exact GlobalTheory.CuspAE.constTermOn_convR hc hl hm hi hf hs x

end GlobalTheory.ConstantTermL2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionComplementTranslatesLocallyConstStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRestriction_complement_translates_locallyConstant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ e, IsSplitIdem D e → ∀ f, IsThetaFunO ψ V W f → ∃ (L : AddSubgroup (halfMx (cA D e) W.rank r)) (Kc : Set (halfMx (cA D e) W.rank r)), IsOpen (L : Set (halfMx (cA D e) W.rank r)) ∧ IsCompact Kc ∧ (∀ t, t ∉ Kc → res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) f) = 0) ∧ ∀ t, ∀ l ∈ L, heisO ψ V W (restEmb V W K (t + l : halfMx (cA D e) W.rank r)) f = heisO ψ V W (restEmb V W K t) f := by
  first | exact @GlobalTheory.HalfSupport.supp_locConst | exact GlobalTheory.HalfSupport.supp_locConst | (intros; apply GlobalTheory.HalfSupport.supp_locConst <;> assumption)
end

