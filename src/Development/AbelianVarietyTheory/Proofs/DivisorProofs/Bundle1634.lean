module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
public import Formalism.LocalToGlobal.Divisibility.NumbersLink
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0752
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundamentalDomainProdLtTop
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

namespace GlobalTheory

theorem isFundamentalDomain_stdDom_prod {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂]
    [IsTopologicalGroup G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂]
    (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) [DiscreteTopology Γ₁] [DiscreteTopology Γ₂] (μ : Measure (G₁ × G₂)) :
    IsFundamentalDomain (Γ₁.prod Γ₂) (GlobalTheory.AutomorphicL2Unitary.stdDom Γ₁ ×ˢ GlobalTheory.AutomorphicL2Unitary.stdDom Γ₂) μ := by
  refine .mk' ((GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom Γ₁).prod (GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom Γ₂)).nullMeasurableSet ?_
  rintro ⟨a, b⟩
  obtain ⟨γ₁, h₁, u₁⟩ := GlobalTheory.AutomorphicL2Unitary.existsUnique_stdDom Γ₁ a
  obtain ⟨γ₂, h₂, u₂⟩ := GlobalTheory.AutomorphicL2Unitary.existsUnique_stdDom Γ₂ b
  refine ⟨⟨((γ₁ : G₁), (γ₂ : G₂)), Subgroup.mem_prod.2 ⟨γ₁.2, γ₂.2⟩⟩, ⟨h₁, h₂⟩, ?_⟩
  rintro ⟨⟨c, d⟩, hcd⟩ ⟨hc, hd⟩
  have e₁ := u₁ ⟨c, (Subgroup.mem_prod.1 hcd).1⟩ hc
  have e₂ := u₂ ⟨d, (Subgroup.mem_prod.1 hcd).2⟩ hd
  ext <;> simp [← e₁, ← e₂]

theorem measure_fundamentalDomain_prod_lt_top : ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂] [MeasurableSpace G₂] [BorelSpace G₂] (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) [DiscreteTopology Γ₁] [DiscreteTopology Γ₂], (∀ μ : Measure G₁, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₁ 𝓕 μ → μ 𝓕 ≠ ⊤) → (∀ μ : Measure G₂, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₂ 𝓕 μ → μ 𝓕 ≠ ⊤) → ∀ μ : Measure (G₁ × G₂), μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain (Γ₁.prod Γ₂) 𝓕 μ → μ 𝓕 < ⊤ := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Γ₁ Γ₂ _ _ h₁ h₂ μ hμ 𝓕 h𝓕
  have hd := GlobalTheory.isFundamentalDomain_stdDom_prod Γ₁ Γ₂ μ
  haveI : Countable (Γ₁.prod Γ₂) := by
    have : Function.Injective (fun γ : Γ₁.prod Γ₂ => ((⟨(γ : G₁ × G₂).1, (Subgroup.mem_prod.1 γ.2).1⟩ : Γ₁),
      (⟨(γ : G₁ × G₂).2, (Subgroup.mem_prod.1 γ.2).2⟩ : Γ₂))) := by
      rintro ⟨⟨a, b⟩, _⟩ ⟨⟨c, d⟩, _⟩ h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      ext <;> simp [h.1, h.2]
    exact this.countable
  rw [h𝓕.measure_eq hd]
  have hp : (Measure.haar : Measure G₁).prod (Measure.haar : Measure G₂) |>.IsHaarMeasure := inferInstance
  rw [Measure.isMulLeftInvariant_eq_smul μ ((Measure.haar : Measure G₁).prod (Measure.haar : Measure G₂)),
    Measure.smul_apply, Measure.prod_prod, ENNReal.smul_def, smul_eq_mul]
  have a₁ := h₁ Measure.haar inferInstance _ (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom Γ₁ Measure.haar)
  have a₂ := h₂ Measure.haar inferInstance _ (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom Γ₂ Measure.haar)
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top a₁.lt_top a₂.lt_top)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicLatticeAtFinitePlaceIffInertStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adelicLatticeAtFinitePlace_iff_inert : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {d : ℕ} (W : Spc F E d) (z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
  z ∈ GlobalTheory.InertSph.latAt W v ↔ ∃ u ∈ GlobalTheory.LFun.latAt w W.L, z = fun i => GlobalTheory.InertBigCell.iotaW hw (u i) := by
  first | exact @GlobalTheory.InertSphLat.mem_latAt_iff | exact GlobalTheory.InertSphLat.mem_latAt_iff | (intros; apply GlobalTheory.InertSphLat.mem_latAt_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalLatticeIdealMapSmulIffGeneratorStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_localLattice_idealMap_smul_iff_generator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 F)) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v), (∀ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) ≤ Valued.v z) → (∃ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) = Valued.v z) → ∀ y : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E, y ∈ GlobalTheory.AdelicU.latLoc F (I.map (algebraMap (𝓞 F) (𝓞 E)) • L) v ↔ ∃ x ∈ GlobalTheory.AdelicU.latLoc F L v, y = z • x := by
  first | exact @GlobalTheory.LatLocIdealSmul.mem_latLoc_idealMap_smul_iff | exact GlobalTheory.LatLocIdealSmul.mem_latLoc_idealMap_smul_iff | (intros; apply GlobalTheory.LatLocIdealSmul.mem_latLoc_idealMap_smul_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberRowsOfKernelDatumSizes
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRows

theorem rowsBody_of_kerTies : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) [_root_.NumberField.IsTotallyComplex t.X.K] (W : Formalism.L2.Col.Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) (hX : t.X.Ok) (Bs : DefBase t.X.K) (Df : DefSide Bs) (Xg : Finset (Formalism.L2.Col.G0 t.X.E t.Pr.vGs D.R.r → t.X.K)) (tup : Bs.Tup → D.what₂.Tup) (hP : ∀ τ, (mtildeGSD W t.Ch t.sel (t.tup (tup τ)) (rPsymF (R := D.R) t.Ch)).Ok) (b : ∀ τ, D.what₂.Word → (t.idx (tup τ)).β (t.m2 + 1)) (hY : ∀ τ x, YbHyp (R := D.R) t.sel (t.tup (tup τ)) (t.cst (tup τ)) (t.idx (tup τ)) (t.word x) t.m2 (b τ x)) (hK : ∀ τ x, KerEquivC W t.Ch t.sel (t.tup (tup τ)) (t.cst (tup τ)) (t.idx (tup τ)) t.amb (t.word x) t.m2 (b τ x) (hY τ x) (rPsymF (R := D.R) t.Ch)) (hF : ∀ τ x j, (chF W t.sel (t.tup (tup τ)) (t.idx (tup τ)) (t.word x) j).Ok) (hE : ∀ x, (evGSD W t.Ch t.sel (t.tup (tup Bs.μ0)) (rPsymF (R := D.R) t.Ch) (t.word x)).Ok) (ev : ∀ τ, (Fin (Df.nV τ) → t.X.K) →ₗ[t.X.K] V0X W t.Ch t.sel (t.tup (tup τ)) Xg (rPsymF (R := D.R) t.Ch)) (u : D.what₂.Word) (eJ : Bs.J ≃ Fin D.R.m) (Nc lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) Nc lam0 c0 ce Ch Sw C1), tup Bs.μ0 = D.what₂.mu0 → KerTies t W Del h0 → KerSizes t W Del h0 CY CT → C0 ≤ Ch → (∀ v : InfinitePlace t.X.K, ((Df.HV Bs.μ0).map v.embedding).PosDef) → (∀ X0, IsFrames Df X0 → ∀ v F, ((mtildeGSD W t.Ch t.sel (t.tup (tup Bs.μ0)) (rPsymF (R := D.R) t.Ch)).ipAt (hP Bs.μ0) v ((ev Bs.μ0 F).1).1 ((ev Bs.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun t.X.K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody (colFace hX Df Xg (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) (fun τ => t.idx_ok (tup τ)) hP D.what₂.Word t.word b hY (kerRec (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) t.word b hY t.amb hK) hF ev) u (memQ (A := (kerRec (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) t.word b hY t.amb hK)) (hF := hF) hE (x := u)) (colsIn W t.Ch hX t.sel (t.tup (tup Bs.μ0)) (t.cst (tup Bs.μ0)) (t.idx (tup Bs.μ0)) (t.idx_ok (tup Bs.μ0)) (t.word u)) (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (D.mem u).A.T Nc lam0 c0 ce Ch Sw C1 H) ∧ ∀ v, IsUnit ((MramH W t.Ch hX (t.word u)).X v).det := by
  intro CY CT hCT
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.columnsMemberRows_of_logLevel_le CY CT hCT
  refine ⟨C0, fun D L hT Gi Gl K Y cX ex t _ W Del h0 hX Bs Df Xg tup hP b hY hK hF hE ev u eJ Nc lam0 c0 ce Ch Sw C1 H hmu hTi hS hC hPD hFr => ?_⟩
  obtain ⟨pl, hpl⟩ := hTi.wts
  have hmu0 : t.tup (tup Bs.μ0) = 1 := hmu ▸ hTi.mu0
  have hsh : (t.cst (tup Bs.μ0)).sharp = true := by rw [hmu]; exact hTi.sharp
  have hfld : FieldOfDefinition W t.sel (t.tup (tup Bs.μ0)) (t.cst (tup Bs.μ0)) (t.word u) t.amb := by
    rw [hmu]; exact hTi.fld u
  have hlog : Real.log (t.Pr.T (t.word u) : ℝ) ≤ CT * D.R.m * L.sc.L := by rw [t.T_rec u]; exact hS.logT u
  have hRd : Reads (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (t.Pr.T (t.word u))
      (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (D.mem u).A.T Nc lam0 c0 ce Ch Sw C1 H) := by
    rw [t.T_rec u]; exact NumReads.ofNum_reads _ _ eJ _ _ Nc lam0 c0 ce Ch Sw C1 H
  have hm2 := hTi.m2
  have hcc := t.cc_rec
  have hsz := hS.sizes
  have hrw := hS.what₂ u
  have hho := hTi.host
  have hch := hTi.chr
  have han := hTi.an
  have hwt := hpl u
  clear hTi hS hpl
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, B, χ, χ_ok, idl, idl_ok, χ_rec, cD, X, seam, seam_ok, Pr, pr_ok, g_rec, ChT, sel, S, word, T_rec, tupT, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  dsimp only at *
  subst hm2
  subst hcc
  exact hC0 D (ofRecord D L Del h0) X seam Pr W ChT glob sel S hX Bs Df Xg (fun τ => tupT (tup τ)) (fun τ => cst (tup τ))
    (fun τ => idx (tup τ)) (fun τ => idx_ok (tup τ)) hP D.what₂.Word word b hY δ B χ cD hK hF hE ev pl u (letterOf D L Del h0 u) eJ _
    hho hwt hch han hmu0 hsh hfld hsz hrw hlog hRd hC hPD hFr

end GlobalTheory.ColRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorPolIsHomogeneous
section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.RotJets

theorem det_X_isHomogeneous {σ : Type*} {a : ℕ} (f : Fin a → Fin a → σ) :
    (Matrix.of fun i i' => (MvPolynomial.X (f i i') : MvPolynomial σ ℂ)).det.IsHomogeneous a := by
  rw [Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun e _ => ?_)
  have h1 : (∏ i, (Matrix.of fun i i' => (MvPolynomial.X (f i i') : MvPolynomial σ ℂ)) (e i) i).IsHomogeneous
      (∑ _i : Fin a, 1) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ (fun i _ => MvPolynomial.isHomogeneous_X ℂ _)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1
  have h0 : (((Equiv.Perm.sign e : ℤ) : MvPolynomial σ ℂ)).IsHomogeneous 0 := by
    have : (((Equiv.Perm.sign e : ℤ) : MvPolynomial σ ℂ)) = MvPolynomial.C ((Equiv.Perm.sign e : ℤ) : ℂ) := by simp
    rw [this]; exact MvPolynomial.isHomogeneous_C _ _
  simpa using h0.mul h1

theorem minorPol_isHomogeneous {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : GlobalTheory.NormSum.Tup D a d n) :
    (GlobalTheory.NormSum.minorPol D T).IsHomogeneous (a * ∑ τ, n τ) := by
  unfold GlobalTheory.NormSum.minorPol
  have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset D.what₂.Tau)
    (fun τ => ∏ j, (Matrix.of fun i i' => (MvPolynomial.X (τ, ((T τ j) : Fin a → Fin d) i, i') :
      MvPolynomial (GL3Theta.Idx D a d) ℂ)).det) (fun τ => ∑ _j : Fin (n τ), a) (fun τ _ =>
      MvPolynomial.IsHomogeneous.prod _ _ _ (fun j _ => det_X_isHomogeneous _))
  convert h using 1
  simp [Finset.mul_sum, mul_comm]

theorem card_of_mem_support {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : GlobalTheory.NormSum.Tup D a d n)
    {α : TaylorLogMetric.Mono D a d} (hα : α ∈ (GlobalTheory.NormSum.minorPol D T).support) :
    Multiset.card (Finsupp.toMultiset α) = a * ∑ τ, n τ := by
  have h := minorPol_isHomogeneous T (MvPolynomial.mem_support_iff.mp hα)
  rw [Finsupp.card_toMultiset]
  rw [← h]
  simp [Finsupp.weight_apply, Finsupp.sum]

end GlobalTheory.RotJets
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Mu0ChiHUnramifiedOutside
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
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

namespace GlobalTheory.TwistUnr

theorem mu0_chiH_unrAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ Lc.Q t → w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      (Lc.C.mu0 j).UnrAt w ∧ (G.ch.chiH (D.R.m - i)).UnrAt w := by
  intro D T Lc sc G μ₀ hL i j t w hw hS
  refine ⟨?_, ?_⟩
  · refine Formalism.L2.Host.IsMu0.unr (Lc.C.isMu0 j) w ?_
    intro k hmemE
    obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t w hw
    haveI : Finite (Formalism.L2.DIV.kP w) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
    have : w.asIdeal.IsPrime := w.isPrime
    haveI : Fintype (Formalism.L2.DIV.kP w) := Fintype.ofFinite _
    have h0g : ((D.host.g k : ℕ) : Formalism.L2.DIV.kP w) = 0 := by
      have := (Ideal.Quotient.eq_zero_iff_mem (I := w.asIdeal)).2 hmemE
      simpa using this
    have h0q : ((q : ℕ) : Formalism.L2.DIV.kP w) = 0 := by
      rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (Formalism.L2.DIV.kP w)
    have hd1 : ringChar (Formalism.L2.DIV.kP w) ∣ D.host.g k := ringChar.dvd h0g
    have hd2 : ringChar (Formalism.L2.DIV.kP w) ∣ q := ringChar.dvd h0q
    have hcop : Nat.Coprime q (D.host.g k) := (Nat.coprime_primes hq (D.host.g_prime k)).2 (hne k)
    have h1 : ringChar (Formalism.L2.DIV.kP w) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd1
    exact CharP.ringChar_ne_one h1
  · have hi := i.isLt
    exact G.ch.unr (D.R.m - (i : ℕ)) (by omega) (Nat.sub_le _ _) w hS

end GlobalTheory.TwistUnr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
section
noncomputable section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area)

namespace GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}

theorem delta_ne_zero (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) : δ ≠ 0 :=
  (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.1

theorem area_pos (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) : 0 < area (lamOf D cc δ) := by
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  rw [GlobalTheory.MomDict.area_lamOf D cc δ h.1.1]
  have h1 : (0 : ℝ) < Ideal.absNorm cc := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h.1.1)
  have h2 := Complex.normSq_pos.2 (delta_ne_zero h)
  have h3 : (0 : ℝ) < Real.sqrt D.host.d := by linarith
  positivity

theorem xiR_pos (D : D7) : 0 < Formalism.L2.Pj.xiR D := by
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  rw [hxi]
  have h1 : (0 : ℝ) < Ideal.absNorm D.host.ccK := by linarith
  have h3 : (0 : ℝ) < Real.sqrt D.host.d := by linarith
  positivity

theorem normSq_scale (hc : cc ≠ ⊥) (h : IsScale D cc r) (δ : ℂ) (τ : D.what₂.Tau) :
    Complex.normSq (δ * embT D τ r) = 2 * Formalism.L2.Pj.xiR D * area (lamOf D cc δ) := by
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  have hcj : embT D τ (D.host.conj r) = starRingEnd ℂ (embT D τ r) := by
    have := D.host.isCMField_hostE
    have h : NumberField.IsCMField.complexConj D.host.E r = D.host.conj r := by
      apply D.host.φ₀.injective
      rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
    rw [← h, NumberField.IsCMField.complexEmbedding_complexConj]
  have h1 := congrArg (embT D τ) h
  rw [map_mul, map_mul, hcj, Complex.mul_conj, map_natCast, map_natCast] at h1
  have h2 : Complex.normSq (embT D τ r) * (Ideal.absNorm D.host.ccK : ℝ) = (Ideal.absNorm cc : ℝ) := by exact_mod_cast h1
  rw [GlobalTheory.MomDict.area_lamOf D cc δ hc, hxi, map_mul, ← h2]
  have h3 : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0 := by linarith
  have h4 : Real.sqrt D.host.d ≠ 0 := by linarith
  field_simp

theorem IsScale.ne_zero (hc : cc ≠ ⊥) (h : IsScale D cc r) : r ≠ 0 := by
  rintro rfl
  have h1 : ((Ideal.absNorm cc : ℕ) : D.host.E) = 0 := by rw [← h]; simp
  exact hc (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))

theorem norm_period_sq (hc : cc ≠ ⊥) (h : IsScale D cc r) (δ : ℂ) (τ : D.what₂.Tau) :
    ‖period D δ r τ‖ ^ 2 = area (lamOf D cc δ) / Real.pi := by
  have hx := xiR_pos D
  have hp := Real.pi_pos
  rw [period, norm_div, div_pow, ← Complex.normSq_eq_norm_sq, normSq_scale hc h, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  field_simp

theorem Hf_scale (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) {a d : ℕ} (Z X : VC D a d) :
    Hf D (tor0 D cc δ) (fun τ i j => δ * embT D τ r * Z τ i j) (fun τ i j => δ * embT D τ r * X τ i j) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (X τ i j) := by
  have hA : ((area (lamOf D cc δ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (area_pos hc).ne'
  have hL : (tor0 D cc δ).abelian₂ = lamOf D cc δ := rfl
  rw [Hf, hL, div_eq_iff hA]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : δ * embT D τ r * starRingEnd ℂ (δ * embT D τ r) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ((area (lamOf D cc δ) : ℝ) : ℂ) := by
    rw [Complex.mul_conj, normSq_scale hc.1.1 h]; push_cast; ring
  rw [map_mul (starRingEnd ℂ) (δ * embT D τ r)]
  linear_combination (Z τ i j * starRingEnd ℂ (X τ i j)) * h1

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem reads_iff (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) (G : VC D S.rank T.rank → ℂ) (f : WO S T → ℂ) :
    Reads ψ θ rfl rfl cc δ r G f ↔ IsThetaFunO ψ S T f ∧ ∀ w : WO S T, w.map (finPart D) = 0 →
      f w = GlobalTheory.FockPos.gaussO θ 1 1 w *
        (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) (GlobalTheory.FockPos.zCo θ 1 1 w) := by
  have hz : ∀ w : WO S T, GlobalTheory.FockPos.zCo θ 1 1 w = fun τ => compAt θ τ w := fun w => by
    funext τ
    have e : ∀ n, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin n) D.host.E) τ = 1 := fun n =>
      Matrix.map_one _ (map_zero _) (map_one _)
    simp only [GlobalTheory.FockPos.zCo, e, inv_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  refine and_congr_right fun _ => forall₂_congr fun w _ => ?_
  have e1 : coordY θ rfl rfl δ r w = fun τ i j => δ * embT D τ r * compAt θ τ w i j := rfl
  have e2 := Hf_scale hc h (fun τ i j => compAt θ τ w i j) (fun τ i j => compAt θ τ w i j)
  rw [e1, e2, GlobalTheory.FockPos.gaussO, hz]
  simp only [Complex.mul_conj']
  congr! 3
  push_cast
  ring

variable {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} {G : VC D a d → ℂ} {f f' : WO S T → ℂ}

theorem Reads.smul (h : Reads ψ θ hS hT cc δ r G f) (c : ℂ) : Reads ψ θ hS hT cc δ r (c • G) (c • f) :=
  ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).smul_mem c h.1, fun w hw => by
    rw [Pi.smul_apply, Pi.smul_apply, h.2 w hw, smul_eq_mul, smul_eq_mul]; ring⟩

theorem Reads.add {G' : VC D a d → ℂ} (h : Reads ψ θ hS hT cc δ r G f) (h' : Reads ψ θ hS hT cc δ r G' f') :
    Reads ψ θ hS hT cc δ r (G + G') (f + f') :=
  ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).add_mem h.1 h'.1, fun w hw => by
    rw [Pi.add_apply, Pi.add_apply, h.2 w hw, h'.2 w hw]; ring⟩

theorem Reads.unique (h : Reads ψ θ hS hT cc δ r G f) (h' : Reads ψ θ hS hT cc δ r G f') : f = f' :=
  sub_eq_zero.1 (GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real ((GlobalTheory.FinWeilO.thetaSub ψ S T).sub_mem h.1 h'.1)
    fun w hw => by rw [Pi.sub_apply, h.2 w hw, h'.2 w hw, sub_self])

end GlobalTheory.NormExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NrmOneNonneg
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

open scoped ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nrm_one_nonneg {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (v : VV ℂ lam) :
    0 ≤ nrm lam (fun _ => 1) v := by
  by_cases hv : v = 0
  · simp [nrm, hv]
  · exact (Complex.le_def.1 (GlobalTheory.CoefModel.pairK_pos lam (fun _ => Matrix.PosDef.one) v hv).le).1

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b C1 : ℝ)

def RatRowAt : Prop := ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m),
  ∃ f : VV D.what₂.LL (wt ch.G (.grid i D.R.m)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.grid (i + 1) D.R.m)), ∀ u,
    ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)

def ConjRowAt : Prop := ∃ a0 nD Gd : ℝ, 0 ≤ a0 ∧ 0 ≤ nD ∧ 0 ≤ Gd ∧ 2 * a0 + (nD + Gd) * C1 * Real.log b ≤ aOne ch.G C b ∧
  ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.grid i D.R.m)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.grid (i + 1) D.R.m))),
    (∀ u, ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ, ∀ u (B : ℝ),
      nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ u) ≤ B →
      nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ (f u)) ≤
        Real.exp (a0 + nD * hArea D ch.S.Z.δ ch.S.Z.t0 ρ + Gd * hTh D ch.S.Z.δ ch.S.Z.t0 ρ) * B

end Claims

end GlobalTheory.KerConjMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelRowsBijectiveOfParts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.PrimIn

theorem principalLevel_rows_bijective_of_parts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → GlobalTheory.LiftRows.UpInj R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → R.PrincipalLevelBijective F := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hOk hW hUp hRow hIn
  have hinj := _root_.GlobalTheory.PrimIn.iC_principal_injective R F hOk hW hIn
  have htop := _root_.GlobalTheory.PrimIn.iC_range_eq_top R F hOk hW hUp hRow hIn
  refine ⟨hinj _, fun t => ⟨hinj t, ?_⟩⟩
  rw [htop t, htop _]

end GlobalTheory.PrimIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPureStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_adelic_eq_span_pure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    schA F κ = Submodule.span ℂ {Φ | ∃ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) ∧
      (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) ∧ Φ = pure f φ} := by
  first | exact @GlobalTheory.WeylSpan.schA_eq_span_pure | exact GlobalTheory.WeylSpan.schA_eq_span_pure | (intros; apply GlobalTheory.WeylSpan.schA_eq_span_pure <;> assumption)
end

