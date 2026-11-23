module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasUnramifiedIntegralFramedPointsOfGoodPlaces
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundCountRankAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankPosNegativeWeightBundle
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.LowPos

open GlobalTheory.FlatTw GlobalTheory.FlatLine

theorem rk_pos {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {G : WTZ D.host.E} (h : Y.GoodAt G)
    {f : Rul Y.d.Xo₂ Y.d.c₂} (hf : f ∈ Y.V G) (hf0 : f ≠ 0) : 0 < Y.rk G := by
  haveI : Module.Finite Y.d.c₂.F (Y.V G) := Module.Finite.of_basis h.1.some.2.1.1
  show 0 < Module.finrank Y.d.c₂.F (Submodule.span Y.d.c₂.F (latW Y.U G : Set (Y.V G)))
  rw [h.2.2, finrank_top]
  exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨f, hf⟩, fun e => hf0 (congrArg Subtype.val e)⟩

theorem mem_cuspW_of_exZ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G G' : WTZ E} (h : exZ Dw G = exZ Dw G') {f : Rul Xo c}
    (hf : f ∈ cuspW Xo c U G) : f ∈ cuspW Xo c U G' := by
  rw [AllWt.mem_cuspW] at hf ⊢
  refine ⟨h ▸ hf.1, fun σ hσ => ?_⟩
  rw [← AllWt.modelWt_congr (U σ) hσ (hU σ hσ) h]
  exact hf.2 σ hσ

theorem exZ_lowered {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (c0 : ℤ) (hn : Even n) :
    exZ Dw (wtOf Dw (uMinus Dw a n kc c0 + parWt Dw (anchor Dw a n kc)) ((n / 2 : ℕ) : ℤ)) = exZ Dw (shiftG Dw a n (-c0)) := by
  obtain ⟨m, rfl⟩ := hn
  have h2 : m + m = 2 * m := by ring
  rw [h2, Nat.mul_div_cancel_left m two_pos, GlobalTheory.CovTop.Model.exZ_shiftG]
  show exZ Dw (wtOf Dw _ _) = exZ Dw (wtOf Dw _ _)
  congr 2
  rw [uMinus, ← uWt_add_anchor Dw a (2 * m) kc, neg_smul]
  abel

end GlobalTheory.CovTop.LowPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudCoordinateConstantAdditiveInCharacter
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

theorem dlog_const_add {S S' : Type} [CommRing S] [CommRing S'] (π : S →+* S') (δ : S → S')
    (hδ : ∀ x y, δ (x * y) = π x * δ y + π y * δ x) (u₁ u₂ u₃ t : Sˣ) (hu : u₃ * t = u₁ * u₂)
    (k₁ k₂ k₃ : S') (h₁ : δ u₁ = π u₁ * k₁) (h₂ : δ u₂ = π u₂ * k₂) (h₃ : δ u₃ = π u₃ * k₃) (ht : δ t = 0) :
    k₃ = k₁ + k₂ := by
  have e := congrArg δ (congrArg Units.val hu)
  simp only [Units.val_mul, hδ, h₁, h₂, h₃, ht] at e
  have hπ := congrArg π (congrArg Units.val hu)
  simp only [Units.val_mul, map_mul] at hπ
  have hunit : IsUnit (π u₃ * π t) := by simpa only [Units.val_mul, map_mul] using (u₃ * t).isUnit.map π
  apply hunit.mul_left_cancel
  linear_combination e - (k₁ + k₂) * hπ

theorem coordEq_const_add : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → Commutes Q m₀ ed → ∀ (α β : Q.X) (c₁ c₂ c₃ : K), CoordEq Y h ν m₀ V pb α c₁ → CoordEq Y h ν m₀ V pb β c₂ → CoordEq Y h ν m₀ V pb (α + β) c₃ → c₃ = c₁ + c₂ := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hC hD hCm α β c₁ c₂ c₃ H₁ H₂ H₃
  obtain ⟨hd, hcov, hV, -⟩ := hC
  have P := hF.pull.1
  let z : Sp K := IsLocalRing.closedPoint K
  let a : Sp K ⟶ Y.H.left := spMap φ ≫ η[Y.H].left
  have hb : (spMap φ ≫ η[Q.P.A].left) ≫ Q.P.A.hom = 𝟙 (Sp K) ≫ spMap φ := by
    rw [Category.assoc, Over.w η[Q.P.A], Category.id_comp]
    rfl
  let b : Sp K ⟶ A₀.left := P.lift _ _ hb
  have hbm : b ≫ m₀ = spMap φ ≫ η[Q.P.A].left := P.lift_fst _ _ _
  have hbA : b ≫ A₀.hom = 𝟙 _ := P.lift_snd _ _ _
  have w : a ≫ Y.q.left = b ≫ m₀ := by
    have := Y.q_linear.isMonHom
    rw [hbm, Category.assoc, ← Over.comp_left, IsMonHom.one_hom]
  have hA3 : ∀ χ : Q.X, η[Q.P.A].left ≫ Q.famφB χ 3 = η[Q.P.A].left := fun χ => by
    change η[Q.P.A].left ≫ (toUnit Q.P.A ≫ η[Q.P.A]).left = _
    rw [← Over.comp_left, ← Category.assoc, toUnit_unique (η[Q.P.A] ≫ toUnit Q.P.A) (𝟙 _), Category.id_comp]
  have hA12 : ∀ χ : Q.X, η[Q.P.A].left ≫ Q.famφB χ 1 = η[Q.P.A].left ≫ Q.famφB χ 2 := fun χ => by
    change η[Q.P.A].left ≫ (padd Q.P.A (𝟙 Q.P.A) (toUnit _ ≫ Q.c χ)).left = η[Q.P.A].left ≫ (toUnit Q.P.A ≫ Q.c χ).left
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    change η[Q.P.A] ≫ (𝟙 Q.P.A * (toUnit _ ≫ Q.c χ)) = _
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc η[Q.P.A] (toUnit _), toUnit_unique (η[Q.P.A] ≫ toUnit Q.P.A) (𝟙 _),
      Category.id_comp]
    have e1 : (η[Q.P.A] : 𝟙_ _ ⟶ Q.P.A) = 1 := by rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [e1, _root_.one_mul]
  have hTb : ∀ (χ : Q.X) (j : Fin 4) (T' : A₀.left ⟶ A₀.left), T' ≫ m₀ = m₀ ≫ Q.famφB χ j → T' ≫ A₀.hom = A₀.hom →
      b ≫ T' ≫ m₀ = spMap φ ≫ η[Q.P.A].left ≫ Q.famφB χ j := fun χ j T' h₁ _ => by
    rw [h₁, reassoc_of% hbm]
  have e3 : ∀ (χ : Q.X) (T' : A₀.left ⟶ A₀.left), T' ≫ m₀ = m₀ ≫ Q.famφB χ 3 → T' ≫ A₀.hom = A₀.hom → b ≫ T' = b :=
    fun χ T' h₁ h₂ => P.hom_ext (by rw [Category.assoc, hTb χ 3 T' h₁ h₂, hA3, hbm]) (by rw [Category.assoc, h₂])
  have e0 : ∀ (χ : Q.X) (T' : A₀.left ⟶ A₀.left), T' ≫ m₀ = m₀ ≫ Q.famφB χ 0 → T' ≫ A₀.hom = A₀.hom → b ≫ T' = b :=
    fun χ T' h₁ h₂ => by rw [hF.T_zero h₁ h₂, Category.comp_id]
  have e12 : ∀ (χ : Q.X) (T₁ T₂ : A₀.left ⟶ A₀.left), T₁ ≫ m₀ = m₀ ≫ Q.famφB χ 1 → T₁ ≫ A₀.hom = A₀.hom →
      T₂ ≫ m₀ = m₀ ≫ Q.famφB χ 2 → T₂ ≫ A₀.hom = A₀.hom → b ≫ T₁ = b ≫ T₂ :=
    fun χ T₁ T₂ h₁ h₂ h₃ h₄ => P.hom_ext (by rw [Category.assoc, Category.assoc, hTb χ 1 T₁ h₁ h₂, hTb χ 2 T₂ h₃ h₄, hA12])
      (by rw [Category.assoc, Category.assoc, h₂, h₄])
  have hcov' : ∀ p : Q.P.A.left, ∃ i, p ∈ V i := fun p => by
    have : p ∈ (⨆ i, V i) := by rw [hcov]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  choose I hI using hcov'
  let p₀ : Q.P.A.left := (b ≫ m₀) z
  let i₀ : h.J := I p₀
  let y : Y.H.left := a z
  have hy : Y.q.left y = p₀ := by
    change (a ≫ Y.q.left) z = _
    rw [w]
  have h₀ : a z ∈ h.W i₀ := by
    rw [hD.1 i₀]
    change Y.q.left y ∈ V i₀
    rw [hy]
    exact hI p₀
  obtain ⟨δ, -, δmul, δeq⟩ := exists_stalkDer_field (isField_dE h ν hF.field i₀) a z h₀
  let π := (a.stalkMap z).hom
  let g := Y.Φ Y.H (𝟙 _)
  let J : (Y.H.left ⟶ Q.P.A.left) → Q.P.L.ι := fun ψ => h.j (I (ψ y))
  have hJ : Good Q.P.L y J := fun ψ => hV _ (hI _)
  have key : ∀ (χ : Q.X) (c : K), CoordEq Y h ν m₀ V pb χ c →
      δ (GlobalTheory.TorusModel.cv (Y.Φ Y.H (𝟙 _)) χ y J).val =
        π (GlobalTheory.TorusModel.cv (Y.Φ Y.H (𝟙 _)) χ y J).val * cst (b ≫ A₀.hom) z c := by
    intro χ c Hc
    obtain ⟨T, hT1, hT2⟩ := hF.exists_strictHenselian_absolutely_closed_local_ring χ
    have f0 := e0 χ (T 0) (hT1 0) (hT2 0)
    have f3 := e3 χ (T 3) (hT1 3) (hT2 3)
    have f12 := e12 χ (T 1) (T 2) (hT1 1) (hT2 1) (hT1 2) (hT2 2)
    let i₁ : h.J := I (((b ≫ T 1) ≫ m₀) z)
    let i : Fin 4 → h.J := ![i₀, i₁, i₁, i₀]
    have hpt : ∀ j, (b ≫ T j ≫ m₀) z = Q.famφB χ j p₀ := fun j => by
      rw [hT1 j, ← Category.assoc]; rfl
    have hIi : ∀ j, I ((b ≫ T j ≫ m₀) z) = i j := by
      intro j; fin_cases j
      · show I ((b ≫ T 0 ≫ m₀) z) = i₀; rw [← Category.assoc, f0]
      · show I ((b ≫ T 1 ≫ m₀) z) = i₁; rw [← Category.assoc]
      · show I ((b ≫ T 2 ≫ m₀) z) = i₁; rw [← Category.assoc, ← f12]
      · show I ((b ≫ T 3 ≫ m₀) z) = i₀; rw [← Category.assoc, f3]
    have hi : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i j) := fun j => hIi j ▸ hI _
    have Hc' := Hc T hT1 hT2 (Sp K) a b w z i hi
    have hm := hF.mem_chart hD hV hT1 w hi
    unfold CoordAt at Hc'
    have hP : ∀ w' : (Sp K).presheaf.stalk z, - gs (b ≫ T 0) z (m₀ ⁻¹ᵁ V (i 0)) (pb (i 0)) +
        gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V (i 1)) (pb (i 1)) - gs (b ≫ T 2) z (m₀ ⁻¹ᵁ V (i 2)) (pb (i 2)) +
        gs (b ≫ T 3) z (m₀ ⁻¹ᵁ V (i 3)) (pb (i 3)) + w' = w' := by
      intro w'
      rw [f0, f3, ← f12]
      show - gs b z (m₀ ⁻¹ᵁ V i₀) (pb i₀) + gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V i₁) (pb i₁) -
        gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V i₁) (pb i₁) + gs b z (m₀ ⁻¹ᵁ V i₀) (pb i₀) + w' = w'
      ring
    rw [hP] at Hc'
    have hcv : (GlobalTheory.TorusModel.cv (Y.Φ Y.H (𝟙 _)) χ y J).val =
        gs (𝟙 _) y (xU Y χ fun j => h.j (i j)) (xc Y χ fun j => h.j (i j)).val := by
      rw [gs_unit (𝟙 _) y _ hm.2]
      congr 1
      refine val_of _ _ _ _ _ fun k => ?_
      show h.j (I ((𝟙 _ ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b χ k) y)) = h.j (i (![1, 2, 0, 3] k))
      rw [Category.id_comp, gtφT_eq, ← hIi, hpt]
      show h.j (I (Q.famφB χ _ (Y.q.left y))) = _
      rw [hy]
    calc δ (GlobalTheory.TorusModel.cv (Y.Φ Y.H (𝟙 _)) χ y J).val
        = δ (gs (𝟙 _) y (h.W i₀ ⊓ xU Y χ fun j => h.j (i j))
            (rsT (xc Y χ fun j => h.j (i j)).val (h.W i₀ ⊓ xU Y χ fun j => h.j (i j)))) := by
          rw [hcv, GlobalTheory.KS.DlogPol.gs_rsT (𝟙 Y.H.left) y (O := h.W i₀ ⊓ xU Y χ fun j => h.j (i j)) inf_le_right hm]
      _ = gs a z (h.W i₀ ⊓ xU Y χ fun j => h.j (i j)) (dE h ν i₀ _
            (rsT (xc Y χ fun j => h.j (i j)).val (h.W i₀ ⊓ xU Y χ fun j => h.j (i j)))) := δeq _ inf_le_left hm _
      _ = gs a z (xU Y χ fun j => h.j (i j)) (xc Y χ fun j => h.j (i j)).val * cst (b ≫ A₀.hom) z c := Hc'
      _ = _ := by rw [gs_stalkMap a z _ hm.2, ← hcv]
  have hθ : δ (ReciprocityTheory.ChartRestriction.G.DVR.th Q y J (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H α) (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H β)
      (Y.Φ Y.H (𝟙 _)).b).val = 0 := by
    let Λ : Q.P.A ⟶ Q.P.A ⊗ (Q.P.A ⊗ Q.P.A) :=
      lift (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Q.P.A α) (lift (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Q.P.A β) (𝟙 _))
    let G := LB.pullGen Q.P.L (thφ Q.P.A (x3 Q.P.A)) thε Q.cub.t Λ.left
    have a1 : ∀ χ, Y.q ≫ ReciprocityTheory.ChartRestriction.G.DVR.cP Q Q.P.A χ = ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H χ := fun χ => by
      simp only [ReciprocityTheory.ChartRestriction.G.DVR.cP, comp_toUnit_assoc]
    have e₁ : ReciprocityTheory.ChartRestriction.G.DVR.th Q y J (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H α) (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H β)
        (Y.Φ Y.H (𝟙 _)).b = val G Y.q.left y J := by
      refine Eq.trans ?_ (val_cub Q.cub Y.q hJ _ _ _).symm
      rw [a1, a1, Category.comp_id]
      rfl
    let j₀ := fun k => J (Y.q.left ≫ Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k)
    let Wc := LB.wchart Q.P.L (fun k => Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) j₀
    let θ₀ : Γ(Q.P.A.left, Wc)ˣ := G.s j₀
    have hWc : Y.q.left y ∈ Wc := hJ.mem _ Y.q.left
    have hp₀W : p₀ ∈ Wc := hy ▸ hWc
    let U : Q.P.A.left.Opens := V i₀ ⊓ Wc
    have hp₀U : p₀ ∈ U := ⟨hI p₀, hp₀W⟩
    have hyU : Y.q.left y ∈ U := hy ▸ hp₀U
    let f : Γ(Q.P.A.left, U) := resG Q.P.A.left (inf_le_right : U ≤ Wc) θ₀.val
    have s1 : (val G Y.q.left y J).val = gs (𝟙 _) y (Y.q.left ⁻¹ᵁ U) ((Y.q.left.app U).hom f) := by
      rw [gs_pull (𝟙 _) Y.q.left y U hyU f, Category.id_comp, gs_res Y.q.left y inf_le_right hyU]
      exact (gs_unit _ _ _ hWc _).symm
    have hle : Y.q.left ⁻¹ᵁ U ≤ h.W i₀ := by
      rw [hD.1 i₀]; exact fun x hx => hx.1
    have s2 := δeq (Y.q.left ⁻¹ᵁ U) hle hyU ((Y.q.left.app U).hom f)
    have s3 := hD.2.1 (Sp K) a b w z i₀ U inf_le_left hp₀U f
    obtain ⟨T, hT1, hT2⟩ := hF.exists_strictHenselian_absolutely_closed_local_ring α
    have f3 := e3 α (T 3) (hT1 3) (hT2 3)
    have hmem3 : (b ≫ T 3 ≫ m₀) z ∈ U := by rw [← Category.assoc, f3]; exact hp₀U
    have s4 := hCm α 3 (T 3) (hT1 3) (hT2 3) U f (Sp K) b z hmem3
    rw [f3] at s4
    have hfix : Q.famφB α 3 p₀ = p₀ := by
      have : (b ≫ T 3 ≫ m₀) z = Q.famφB α 3 p₀ := by rw [hT1 3, ← Category.assoc]; rfl
      rw [← this, ← Category.assoc, f3]
    obtain ⟨δ', -, δ'mul, δ'eq⟩ := exists_stalkDer_along hd b z
    have hc3 : (b ≫ m₀) z ∈ Q.famφB α 3 ⁻¹ᵁ U := by
      show Q.famφB α 3 p₀ ∈ U; rw [hfix]; exact hp₀U
    have s5 := δ'eq _ hc3 ((Q.famφB α 3).app U |>.hom f)
    let C3 : Q.P.A ⟶ Q.P.A := toUnit Q.P.A ≫ η[Q.P.A]
    let J' : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι := fun ψ => h.j (I (ψ p₀))
    have hJ' : Good Q.P.L p₀ J' := fun ψ => hV _ (hI _)
    have hc3' : C3.left p₀ ∈ Wc := by
      show Q.famφB α 3 p₀ ∈ Wc; rw [hfix]; exact hp₀W
    have s6 : gs (𝟙 _) ((b ≫ m₀) z) (Q.famφB α 3 ⁻¹ᵁ U) ((Q.famφB α 3).app U |>.hom f) = 1 := by
      change gs (𝟙 _) p₀ (C3.left ⁻¹ᵁ U) ((C3.left.app U).hom f) = 1
      rw [gs_pull (𝟙 _) C3.left p₀ U (hfix.symm ▸ hp₀U) f, Category.id_comp,
        gs_res C3.left p₀ inf_le_right (hfix.symm ▸ hp₀U), gs_unit _ _ _ hc3']
      have v := val_of G C3.left p₀ J' j₀ fun k => by
        show h.j (I ((C3.left ≫ Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) p₀)) =
          h.j (I ((Y.q.left ≫ Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) y))
        show h.j (I ((Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) (C3.left p₀))) =
          h.j (I ((Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) (Y.q.left y)))
        rw [hy]; exact congrArg (fun p => h.j (I ((Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) p))) hfix
      refine (congrArg Units.val v.symm).trans ?_
      rw [val_cub Q.cub C3 hJ' _ _ _, Category.comp_id, show C3 = 1 from Hom.one_def.symm]
      have face3 (x y : Q.P.A ⟶ Q.P.A) : cubV Q.cub p₀ J' x y 1 = 1 := by
        have e := val_corr hJ' (Q.cub.face 2) (lift x y).left
        rw [val_one] at e
        refine Eq.trans ?_ e
        refine Eq.trans ?_ (val_cub Q.cub (lift x y) hJ' (x2 Q.P.A 0) (x2 Q.P.A 1) (pzero Q.P.A _)).symm
        congr 1 <;> simp [x2, pzero, Hom.one_def]
      rw [face3, Units.val_one]
    have δ'1 : δ' 1 = 0 := by
      have := δ'mul 1 1
      simp only [_root_.mul_one, map_one, _root_.one_mul] at this
      linear_combination -this
    rw [e₁, s1, s2, ← s3, ← s4, ← s5, s6, δ'1]
  have E := dlog_const_add π δ δmul _ _ _ _ (GlobalTheory.TorusModel.cv_add (Y.Φ Y.H (𝟙 _)) hJ α β) _ _ _
    (key α c₁ H₁) (key β c₂ H₂) (key (α + β) c₃ H₃) hθ
  rw [cst_eq_cstH, cst_eq_cstH, cst_eq_cstH, ← map_add (f := _)] at E
  exact (cstH (b ≫ A₀.hom) z).injective E

end GlobalTheory.HeatConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudCoordinateInChartsHasCharacterWeight
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false

namespace GlobalTheory.HeatConn.CoordWt

theorem isWt_xc : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (α : Q.X) (t : Fin 4 → Q.P.L.ι) (W : Y.H.left.Opens), W ≤ xU Y α t → IsWt Y α W (rsT (xc Y α t).val W) := by
  intro R _ _ Q O _ _ _ oa Y α t W hW
  intro S _ φ x x' c a a' ha ha' hV₁ hV₂ hq hc
  subst ha ha'
  have germ : ∀ (b : Sp S ⟶ Y.H.left), ⊤ ≤ b ⁻¹ᵁ W → ∀ z,
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (valR b W (rsT (xc Y α t).val W))) =
        gs b z (xU Y α t) (xc Y α t).val := by
    intro b hb z
    rw [valR, dite_eq_left hb, Iso.hom_inv_id_apply, rsT, dite_eq_left hW]
    refine (gs_res (𝟙 _) z hb trivial _).trans ((gs_pull (𝟙 _) b z W (hb trivial) _).trans ?_)
    rw [Category.id_comp]
    exact gs_res b z hW (hb trivial) _
  have key : ∀ (xx : Over.mk (spMap φ) ⟶ Y.H), ⊤ ≤ xx.left ⁻¹ᵁ W → ∀ z J, Good Q.P.L z J →
      gs xx.left z (xU Y α t) (xc Y α t).val =
        (trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε xx.left z (fun k => t (![1, 2, 0, 3] k))
          (fun k => J (xx.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k))).val *
        (val ((Y.Φ _ xx).s α) (𝟙 _) z J).val := by
    intro xx hb z J hJ
    have hp := ((GlobalTheory.TorusModel.isPull_iff xx _ _).1 (Y.rep.1 _ _ xx (𝟙 _))).2 α z J hJ
    rw [Category.comp_id] at hp
    have hmem : xx.left z ∈ xU Y α t := hW (hb trivial)
    rw [gs_unit xx.left z _ hmem, gen_trans ((Y.Φ Y.H (𝟙 _)).isGen α) xx.left z hmem (hJ.mem _ xx.left), Units.val_mul]
    congr 1
    exact congrArg Units.val hp.symm
  have hqq : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := congrArg CommaMorphism.left hq
  have hφ : ∀ k, x'.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k = x.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k :=
    fun k => by rw [gtφT_eq, ← Category.assoc, hqq, Category.assoc]
  have htr : ∀ z (J : (Sp S ⟶ Q.P.A.left) → Q.P.L.ι),
      trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε x'.left z (fun k => t (![1, 2, 0, 3] k))
          (fun k => J (x'.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k)) =
        trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε x.left z (fun k => t (![1, 2, 0, 3] k))
          (fun k => J (x.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k)) := by
    intro z J
    unfold trF
    refine Finset.prod_congr rfl fun k _ => ?_
    beta_reduce
    rw [hφ k]
  apply (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
  refine fn_ext fun z _ => ?_
  obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a _ _ => a.elim) (fun k => k.elim)
  show gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _) =
    gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _)
  rw [map_mul, gs_mul (𝟙 _) z ⊤ trivial, germ _ hV₂ z, germ _ hV₁ z, key x' hV₂ z J hJ, key x hV₁ z J hJ, htr,
    hc α z J hJ, show (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c α : S) = (unitOn (c α)).val from rfl,
    gs_unit (𝟙 _) z ⊤ trivial, Units.val_mul]
  exact _root_.mul_left_comm _ _ _

end GlobalTheory.HeatConn.CoordWt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidifiedBundlePullbackUniversalTriple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullAmpleXF

theorem relAmple_XF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (tF : SAB H (Xo.XF c)) :
    SABMap tF Xo.univ.t (pullback.fst _ _) → RelAmple tF.G tF.PP.L := by
  intro mF
  have hP : IsProper tF.G.hom := MorphismProperty.of_isPullback (P := @IsProper) mF.cart.1 Xo.univ.proper
  obtain ⟨w, hw, -⟩ := mF.lin
  refine GlobalTheory.AmpleLocal.relAmple_of_locally _ tF.G tF.PP.L tF.PP.isLB inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := Xo.X) (U := ⊤)
    (x := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) s) trivial
  let f := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
  let U := f ⁻¹ᵁ V
  refine ⟨U, hs, ?_⟩
  have H : IsPullback ((tF.G.hom ⁻¹ᵁ U).ι ≫ mF.φ) (tF.G.hom ∣_ U) Xo.univ.t.G.hom (U.ι ≫ f) :=
    (isPullback_morphismRestrict tF.G.hom U).flip.paste_horiz mF.cart.1
  obtain ⟨w', hw'⟩ : LBIso (tF.PP.L.pull (tF.G.hom ⁻¹ᵁ U).ι) (Xo.univ.t.PP.L.pull ((tF.G.hom ⁻¹ᵁ U).ι ≫ mF.φ)) :=
    LBIso.chartPull (chartPullPull _ _)
      (chartPullSame Xo.univ.t.PP.L (fun _ : PUnit => (tF.G.hom ⁻¹ᵁ U).ι ≫ mF.φ) (fun _ => mF.φ) (fun _ => 1)
        (tF.G.hom ⁻¹ᵁ U).ι fun _ => rfl) ⟨w, hw⟩
  exact relAmple_pull (A' := Over.mk (tF.G.hom ∣_ U)) H Xo.univ.t.PP.isLB (pull_isLB tF.PP.isLB _)
    ((isGen_iff w').1 hw') V hV (fun y => y.2) Xo.univ.ample

end GlobalTheory.PullAmpleXF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionCountGrowthMetricNearGeneratorMax
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem lc_exp_bounds : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ κ t : ℝ, 0 < κ → κ ≤ 1 → 0 < t → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), P.nu e 0 σ y (x l) ≤ 1) → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, κ ≤ P.nu e 0 σ y (x l)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, gdeg P.L D / D.factorial * t - ε ≤ P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) ∧ P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) ≤ gdeg P.L D / D.factorial * (t - Real.log κ / e) + ε := by
  intro hA k _ X _ p D hp P hL e x hx κ t hκ hκ1 ht h1 h2 ε hε
  have hdeg := _root_.GlobalTheory.HSAmp.finrank_ratF_eq_gdeg hA k X p D hp P hL e x hx
  have hup := _root_.GlobalTheory.HSAmp.HSUpper.upper_bound k X p D hp P hL e x hx
  have hlo := _root_.GlobalTheory.HSAmp.FLower.count_rank_lower k X p D hp P hL e x hx
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hfin : ∀ (m : ℕ) (R : ℝ), 0 ≤ R → (P.Bl m 1 R).Finite := by
    intro m R hR
    obtain ⟨c, C, _, h⟩ := hup m 1
    have := ((h 0).2.2 R κ hR hκ h2).1
    simpa using this
  have key := _root_.GlobalTheory.hsGrowth_exp_radius D e (Module.finrank (ratF x) X.functionField) (fun m R => (P.Bl m 1 R).ncard) κ t
    hx.pos hκ hκ1 ht
    (fun m R R' hR hRR' => Set.ncard_le_ncard
      (fun f hf => ⟨hf.1, fun σ y => (hf.2 σ y).trans hRR'⟩) (hfin m R' (hR.trans hRR')))
    (fun s _ => by
      obtain ⟨c, C, hC, h⟩ := hlo s 1
      obtain ⟨c', C', hC', h'⟩ := hup s 1
      refine ⟨c, c', C, C', hC, hC', fun q R hR => ⟨?_, ?_⟩⟩
      · have h3 := (h q).2 R hR h1
        have hf := hfin (e * (q + c) + s) (C * (q + D).choose D * R) (by positivity)
        have e1 : ((e * (q + c) + s : ℕ) : ℤ) = e * (q + c : ℕ) + s := by push_cast; ring
        rw [← e1, ← hf.cast_ncard_eq] at h3
        exact_mod_cast h3
      · have h3 := ((h' q).2.2 R κ hR hκ h2).2
        have e1 : ((e * q + s : ℕ) : ℤ) = e * q + s := by push_cast; ring
        rw [← e1] at h3
        exact h3) ε hε
  have e2 : (Module.finrank (ratF x) X.functionField : ℝ) / ((e : ℝ) ^ D * D.factorial) =
      gdeg P.L D / D.factorial := by
    rw [hdeg, mul_div_mul_left _ _ (pow_pos he D).ne']
  rw [e2] at key
  exact key

end GlobalTheory.HSAmp
end

