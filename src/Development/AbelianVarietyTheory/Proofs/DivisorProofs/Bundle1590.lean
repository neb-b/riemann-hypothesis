module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEigenpartEqRowsFullHecke
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1511

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupported
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacIso

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem piW_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piW t (cA σ x) = piW (t.comp σ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul a e => rfl

theorem eq_zero_of_at_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v)
    {z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : At (evFin F v) z) (h1 : piW τ z = 0) (h2 : piW (τ.comp σ) z = 0) : z = 0 := by
  have hc : compFin F E v z = 0 :=
    GlobalTheory.AdelicU.split_ext h τ (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)
  have e := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at e
  rw [e, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  change GlobalTheory.EmbChart.tensAt E v ((1 : Fv F v) ⊗ₜ[F] (1 : E)) * z = 0
  rw [GlobalTheory.EmbChart.tensAt_mul_right, hc, mul_zero, map_zero]

theorem symp_self_eq_zero : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (u : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) u →
    (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∨ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0) →
    ∀ ξ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E),
      symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u = 0 := by
  intro D a a' Bs Γ X om om' hTr u hu hpi ξ
  have hcm : IsCMExt D.host.F D.host.E D.sp.cm.sig := hTr.base.cm
  set z := GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u with hzdef
  have hat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) z := by
    intro c hc
    have hij : ∀ i j, c • u i j = 0 := fun i j => by
      have := congrFun (congrFun (hu c hc) i) j
      simpa using this
    simp only [hzdef, GlobalTheory.WeilM.hTens, Finset.smul_sum, ← smul_mul_assoc, hij, zero_mul, Finset.sum_const_zero]
  have first : ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F Bs.v₁, (∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t (u i j) = 0) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t z = 0 := by
    intro t ht
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hzdef, GlobalTheory.WeilM.hTens, map_sum, map_mul, ht, zero_mul, Finset.sum_const_zero]
  have last : ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F Bs.v₁,
      (∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp D.sp.cm.sig) (u i j) = 0) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t z = 0 := by
    intro t ht
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hzdef, GlobalTheory.WeilM.hTens, map_sum, map_mul, GlobalTheory.VacIso.piW_cA, ht, mul_zero, Finset.sum_const_zero]
  have hz0 : z = 0 := by
    rcases hpi with h0 | h0
    · have h0' : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁ (u i j) = 0 := fun i j => by
        simpa using congrFun (congrFun h0 i) j
      refine GlobalTheory.VacIso.eq_zero_of_at_split hcm Bs.τ₁ hat (first _ h0') (last _ ?_)
      rw [GlobalTheory.AdelicU.comp_conj_conj hcm]; exact h0'
    · have h0' : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig) (u i j) = 0 := fun i j => by
        simpa using congrFun (congrFun h0 i) j
      exact GlobalTheory.VacIso.eq_zero_of_at_split hcm Bs.τ₁ hat (last _ h0') (first _ h0')
  simp only [GlobalTheory.WeilM.symp, ← hzdef, hz0, mul_zero, map_zero]

end GlobalTheory.VacIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransferEigensystemPartsThreeLevelsOfMultEq
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open Formalism.IndefR.Lev
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Hk3 (Core IsSF SchurAll EEc Wcc)

namespace GlobalTheory.TrLevMult

theorem level_eq_trivial {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    (L : LevelP Pg r LL) (h : L.H = ⊥) : L = LevelP.triv Pg r LL := by
  obtain ⟨H, chi⟩ := L
  simp only at h
  subst h
  unfold LevelP.triv
  congr 1
  ext x
  have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.mp x.2)
  subst hx
  simp

theorem levPOf_bot_eq {D : D7} {G K : Type} [Group G] [Field K] {Pg : Finset (Pl D.host.E)} {r : ℕ} (eG : G ≃* G0 Pg r)
    (σ : K →+* ℂ) (ψ : (⊥ : Subgroup G) →* Kˣ) : levPOf eG σ ⊥ ψ = LevelP.triv Pg r ℂ := by
  apply level_eq_trivial
  show Subgroup.comap eG.symm.toMonoidHom ⊥ = ⊥
  ext x
  simp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem pg_over {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hSF : IsSF R SF) : ∀ PP ∈ R.Pg, ∃ v ∈ SF,
    PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal :=
  fun PP hPP => ⟨Formalism.IndefR.Fin.belowPl PP, (hSF _).2 ⟨PP, hPP, rfl⟩, rfl⟩

theorem trAt_of_dim (hC : Core R F) {SF} (hSF : IsSF R SF) (i : Fin D.R.m) (Pe Pw : LevelP R.Pg D.R.r ℂ)
    (hdim : ∀ c, Module.finrank ℂ (Wcc R SF i c ⊓ (R.Wat i (sg0 D A) Pw).comap (R.HW i _).e : Submodule ℂ _) =
      Module.finrank ℂ (EEc R SF c ⊓ (R.EEat Pe).comap R.HE.e : Submodule ℂ _)) :
    GlobalTheory.TrCopy.TRAt R SF i Pe Pw := by
  intro c
  have hE : R.EEat Pe ≤ R.EEat R.triv := GlobalTheory.PartDims.goodPart_le_flag (L := R.dat0 R.triv) R.θ _ rfl rfl _ _
  have hW : R.Wat i (sg0 D A) Pw ≤ R.Wat i (sg0 D A) R.triv :=
    GlobalTheory.PartDims.goodPart_le_flag (L := R.datWp i R.triv) R.θ _ rfl rfl _ _
  have kE : ∀ Q d B, Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) SF Q d B ↔
      Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF Q d B :=
    _root_.GlobalTheory.HeckeLevelFree.isHeckeOpFull_withP_iff D (Yc D 0) (R.βY 0) (R.dat0 R.triv) Pe R.triv SF (pg_over hSF)
  have kW : ∀ Q d B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw)) SF Q d B ↔
      Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF Q d B :=
    _root_.GlobalTheory.HeckeLevelFree.isHeckeOpFull_withP_iff D (Wc D i) (R.βW i) (R.datWp i R.triv) Pw R.triv SF (pg_over hSF)
  have eqE : GlobalTheory.TrCopy.partE R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) R.e0 SF c =
      R.EEat Pe ⊓ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF
        (fun Q d => c Q (dualLab d)) := by
    ext x
    show (x ∈ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) SF
        (fun Q d => c Q (dualLab d)) ∧ x ∈ R.EEat Pe) ↔ (x ∈ R.EEat Pe ∧ x ∈ partFull R.θ (R.MY 0)
        (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF (fun Q d => c Q (dualLab d)))
    simp only [partFull, Submodule.mem_inf, Submodule.mem_iInf]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h2, (hE h2).1, fun Q d B hB => h1 Q d B ((kE Q d B).2 hB)⟩
    · rintro ⟨h2, -, h1⟩
      exact ⟨⟨h2.1, fun Q d B hB => h1 Q d B ((kE Q d B).1 hB)⟩, h2⟩
  have eqW : GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw))
        (R.eWf i (sg0 D A)) SF c =
      R.Wat i (sg0 D A) Pw ⊓ partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
        (levChi _ (R.βW i) (R.datWp i R.triv)) SF c := by
    ext x
    show (x ∈ partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw)) SF c ∧
        x ∈ R.Wat i (sg0 D A) Pw) ↔ (x ∈ R.Wat i (sg0 D A) Pw ∧ x ∈ partFull R.θ (R.MW i (sg0 D A))
        (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c)
    simp only [partFull, Submodule.mem_inf, Submodule.mem_iInf]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h2, (hW h2).1, fun Q d B hB => h1 Q d B ((kW Q d B).2 hB)⟩
    · rintro ⟨h2, -, h1⟩
      exact ⟨⟨h2.1, fun Q d B hB => h1 Q d B ((kW Q d B).1 hB)⟩, h2⟩
  have fE := GlobalTheory.PartDims.finrank_comap hC.models.HE (U := R.EEat Pe ⊓ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
    (levChi _ (R.βY 0) (R.dat0 R.triv)) SF (fun Q d => c Q (dualLab d))) (inf_le_left.trans hE)
  have fW := GlobalTheory.PartDims.finrank_comap (hC.models.HW i (sg0 D A)) (U := R.Wat i (sg0 D A) Pw ⊓
    partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c)
    (inf_le_left.trans (hW.trans inf_le_left))
  have cE : (R.EEat Pe ⊓ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
      (levChi _ (R.βY 0) (R.dat0 R.triv)) SF (fun Q d => c Q (dualLab d))).comap R.HE.e =
      EEc R SF c ⊓ (R.EEat Pe).comap R.HE.e := by
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  have cW : (R.Wat i (sg0 D A) Pw ⊓ partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) SF c).comap (R.HW i _).e =
      Wcc R SF i c ⊓ (R.Wat i (sg0 D A) Pw).comap (R.HW i _).e := by
    ext x
    exact ⟨fun hx => ⟨⟨hW hx.1, hx.2⟩, hx.1⟩, fun hx => ⟨hx.2, hx.1.2⟩⟩
  haveI := fE.2
  haveI := fW.2
  show Module.rank ℂ (GlobalTheory.TrCopy.partE R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) R.e0 SF c) =
    Module.rank ℂ (GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw))
        (R.eWf i (sg0 D A)) SF c)
  rw [eqE, eqW, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← fE.1, ← fW.1, cE, cW, hdim c]

end GlobalTheory.TrLevMult


open GlobalTheory.TrLevMult in
theorem GlobalTheory.TrLevMult.trLev_of_multEq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ s : ℕ, A.fam.Ok s → GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → GoodStable A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.TrCopy.TRLev R F SF := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F s hs hC hS hX hD hM SF hSF
  have key : ∀ i (P : Subgroup G) (ψ : P →* D.what₂.LLˣ),
      GlobalTheory.TrCopy.TRAt R SF i (levPOf R.eG D.what₂.embLL P ψ) (levPOf R.eG (sg0 D A) P ψ⁻¹) :=
    fun i P ψ => trAt_of_dim hC hSF i _ _ (fun c => GlobalTheory.DimFull.dim_parts_full R F hs hC hS hX hD hM SF hSF P ψ i c)
  intro i
  refine ⟨?_, fun b => key i _ _⟩
  have h := key i ⊥ 1
  rwa [inv_one, levPOf_bot_eq, levPOf_bot_eq] at h

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportDenom
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThetaDenom


open Formalism.UG in
theorem transport_denom : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)),
    ∃ C : ℝ, ∀ (g : GL (Fin n) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)), ∃ N : ℕ, 0 < N ∧
      (N : ℝ) ≤ C * ((heightGL F g : ℝ) * heightGL F h) ∧
      ∀ (M : ℕ) (y : Fin n × Fin d → AF F), IsMulInt F (M * N) y →
        IsMulInt F M (e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ)).1 ∧
        IsMulInt F M (e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ)).2 := by
  intro F E _ _ _ _ _ n d e
  classical
  set Y : Fin n × Fin d → Matrix (Fin n) (Fin d) (AF F ⊗[F] E) :=
    fun j => e.symm (0, fun k => if j = k then 1 else 0) with hY
  let f1 : Fin n × Fin d → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) :=
    fun i => (LinearMap.proj i).comp ((LinearMap.fst (AF F) _ _).comp e.toLinearMap)
  let f2 : Fin n × Fin d → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) :=
    fun i => (LinearMap.proj i).comp ((LinearMap.snd (AF F) _ _).comp e.toLinearMap)
  choose K1 hK1f hK11 hK1 using fun i => _root_.GlobalTheory.LinFormBound.main (f1 i)
  choose K2 hK2f hK21 hK2 using fun i => _root_.GlobalTheory.LinFormBound.main (f2 i)
  choose KY hKYf hKY1 hKY using fun j => _root_.GlobalTheory.FixedBound.exists_entry_absFin_bound (Y j)
  have prod_one : ∀ (K : Fin n × Fin d → HeightOneSpectrum (𝓞 F) → ℝ≥0), (∀ i v, 1 ≤ K i v) →
      ∀ v, 1 ≤ ∏ i, K i v := fun K hK v => Finset.one_le_prod' fun i _ => hK i v
  have prod_fin : ∀ (K : Fin n × Fin d → HeightOneSpectrum (𝓞 F) → ℝ≥0), (∀ i, (Function.mulSupport (K i)).Finite) →
      (Function.mulSupport fun v => ∏ i, K i v).Finite := fun K hK =>
    ((Finset.univ : Finset (Fin n × Fin d)).finite_toSet.biUnion fun i _ => hK i).subset
      (Finset.mulSupport_prod _ _)
  have single_le : ∀ (K : Fin n × Fin d → HeightOneSpectrum (𝓞 F) → ℝ≥0), (∀ i v, 1 ≤ K i v) →
      ∀ i v, K i v ≤ ∏ i, K i v := fun K hK i v => Finset.single_le_prod' (fun j _ => hK j v) (Finset.mem_univ i)
  set Ka : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => (∏ i, K1 i v) * (∏ i, K2 i v) * ∏ j, KY j v with hKa
  have hKa1 : ∀ v, 1 ≤ Ka v := fun v => one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (prod_one K1 hK11 v) (prod_one K2 hK21 v)) (prod_one KY hKY1 v)
  have hKaf : (Function.mulSupport Ka).Finite :=
    ((((prod_fin K1 hK1f).union (prod_fin K2 hK2f)).subset (Function.mulSupport_mul _ _)).union
      (prod_fin KY hKYf)).subset (Function.mulSupport_mul _ _)
  have hle1 : ∀ i j v, K1 i v * KY j v ≤ Ka v := fun i j v =>
    calc K1 i v * KY j v ≤ (∏ i, K1 i v) * ∏ j, KY j v := mul_le_mul' (single_le K1 hK11 i v) (single_le KY hKY1 j v)
      _ ≤ Ka v := by
        show (∏ i, K1 i v) * ∏ j, KY j v ≤ (∏ i, K1 i v) * (∏ i, K2 i v) * ∏ j, KY j v
        rw [mul_right_comm]
        exact le_mul_of_one_le_right' (prod_one K2 hK21 v)
  have hle2 : ∀ i j v, K2 i v * KY j v ≤ Ka v := fun i j v =>
    calc K2 i v * KY j v ≤ (∏ i, K2 i v) * ∏ j, KY j v := mul_le_mul' (single_le K2 hK21 i v) (single_le KY hKY1 j v)
      _ ≤ Ka v := by
        show (∏ i, K2 i v) * ∏ j, KY j v ≤ (∏ i, K1 i v) * (∏ i, K2 i v) * ∏ j, KY j v
        exact mul_le_mul_left (le_mul_of_one_le_left' (prod_one K1 hK11 v)) _
  refine ⟨((∏ᶠ v, Ka v : ℝ≥0) : ℝ), fun g h => ?_⟩
  set B : HeightOneSpectrum (𝓞 F) → ℝ≥0 :=
    fun v => Ka v * htFin F v (bc (compFin F E v) g) * htFin F v (bc (compFin F E v) h) with hB
  have hB1 : ∀ v, 1 ≤ B v := fun v =>
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hKa1 v) (one_le_htOf _ _)) (one_le_htOf _ _)
  have hgf := finite_mulSupport_htFin F g
  have hhf := finite_mulSupport_htFin F h
  have hBf : (Function.mulSupport B).Finite :=
    (((hKaf.union hgf).subset (Function.mulSupport_mul _ _)).union hhf).subset (Function.mulSupport_mul _ _)
  obtain ⟨N, hN, hNle, hNint⟩ := GlobalTheory.SmoothForms.denom_global B hB1 hBf
  have hfin : ∀ {m : ℕ} (k : GL (Fin m) (AF F ⊗[F] E)), ∏ᶠ v, htFin F v (bc (compFin F E v) k) ≤ heightGL F k :=
    fun k => by
      unfold heightGL
      exact le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _)
  refine ⟨N, hN, ?_, ?_⟩
  · have e1 : ∏ᶠ v, B v = (∏ᶠ v, Ka v) * (∏ᶠ v, htFin F v (bc (compFin F E v) g)) *
        ∏ᶠ v, htFin F v (bc (compFin F E v) h) := by
      rw [hB, finprod_mul_distrib ((hKaf.union hgf).subset (Function.mulSupport_mul _ _)) hhf,
        finprod_mul_distrib hKaf hgf]
    have : (N : ℝ≥0) ≤ (∏ᶠ v, Ka v) * (heightGL F g * heightGL F h) := by
      refine hNle.trans ?_
      rw [e1, mul_assoc]
      exact mul_le_mul_right (mul_le_mul' (hfin g) (hfin h)) _
    exact_mod_cast this
  intro M y hy
  set L : (Fin n × Fin d → AF F) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    e.toLinearMap ∘ₗ sand (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) ∘ₗ
      e.symm.toLinearMap ∘ₗ LinearMap.inr (AF F) _ _ with hL
  have hLy : e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ) =
      ∑ j, y j • L (fun k => if j = k then 1 else 0) := LinearMap.pi_apply_eq_sum_univ L y
  have hsz : ∀ j v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v
      (sand (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) (Y j) p.1 p.2))) ≤
      htFin F v (bc (compFin F E v) g) * KY j v * htFin F v (bc (compFin F E v) h) := fun j v =>
    Finset.sup_le fun p _ => (_root_.GlobalTheory.absFin_mul_mul_transpose_le g (Y j) h v p.1 p.2).trans
      (mul_le_mul_left (mul_le_mul_right (hKY j v) _) _)
  have hcomp : ∀ t : Fin n × Fin d → AF F, (∀ j v, ‖evFin F v (t j)‖₊ ≤ B v) →
      (∑ j, y j * t j).1 = 0 ∧ ∀ v, ‖evFin F v (∑ j, y j * t j)‖ ≤ ‖(M : Fv F v)‖ := by
    intro t ht
    refine ⟨?_, fun v => ?_⟩
    · change fstA F (∑ j, y j * t j) = 0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_mul]
      change (y j).1 * _ = 0
      rw [hy.1 j, zero_mul]
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => ?_
      rw [map_mul, norm_mul]
      have h1 := hy.2 v j
      have h2 := hNint v (evFin F v (t j)) (ht j v)
      rw [Nat.cast_mul, norm_mul] at h1
      rw [norm_mul] at h2
      calc ‖evFin F v (y j)‖ * ‖evFin F v (t j)‖ ≤ ‖(M : Fv F v)‖ * ‖(N : Fv F v)‖ * ‖evFin F v (t j)‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖(M : Fv F v)‖ * (‖(N : Fv F v)‖ * ‖evFin F v (t j)‖) := mul_assoc _ _ _
        _ ≤ ‖(M : Fv F v)‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = ‖(M : Fv F v)‖ := mul_one _
  have htB : ∀ (f : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) (K : HeightOneSpectrum (𝓞 F) → ℝ≥0),
      (∀ X v, ‖evFin F v (f X)‖₊ ≤ K v * Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) →
      (∀ j v, K v * KY j v ≤ Ka v) → ∀ j v,
      ‖evFin F v (f (sand (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) (Y j)))‖₊ ≤ B v := by
    intro f K hf hK j v
    refine (hf _ v).trans ?_
    refine (mul_le_mul_right (hsz j v) _).trans ?_
    calc K v * (htFin F v (bc (compFin F E v) g) * KY j v * htFin F v (bc (compFin F E v) h)) =
        K v * KY j v * htFin F v (bc (compFin F E v) g) * htFin F v (bc (compFin F E v) h) := by ring
      _ ≤ B v := mul_le_mul_left (mul_le_mul_left (hK j v) _) _
  refine ⟨⟨fun i => ?_, fun v i => ?_⟩, ⟨fun i => ?_, fun v i => ?_⟩⟩
  all_goals rw [hLy]
  all_goals simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  · exact (hcomp _ fun j v => htB (f1 i) (K1 i) (hK1 i) (fun j v => hle1 i j v) j v).1
  · exact (hcomp _ fun j v => htB (f1 i) (K1 i) (hK1 i) (fun j v => hle1 i j v) j v).2 v
  · exact (hcomp _ fun j v => htB (f2 i) (K2 i) (hK2 i) (fun j v => hle2 i j v) j v).1
  · exact (hcomp _ fun j v => htB (f2 i) (K2 i) (hK2 i) (fun j v => hle2 i j v) j v).2 v

end GlobalTheory.ThetaDenom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionCosetVectorEqTranslateUnitVector
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.LiftCoset

theorem globalIntegralMatrix_mem_stdThetaLattice (D : D7) (δ : ℂ) {a d : ℕ} (x : Matrix (Fin d) (Fin a) D.host.E)
    (hx : ∀ i j, ∃ b : 𝓞 D.host.E, x i j = (b : D.host.E)) :
    pt D (tor0 D ⊤ δ) δ x ∈ La0 D (tor0 D ⊤ δ) a d := by
  refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, _, ?_, rfl⟩
  refine Submodule.subset_span ⟨1, ?_, _, Submodule.subset_span fun v hv i _ => ?_, (one_smul _ _).symm⟩
  · refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  · have : ∑ j, x i j * v j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := sum_mem fun j _ => by
      obtain ⟨b, hb⟩ := hx i j
      have h1 := (1 : Submodule (𝓞 D.host.E) D.host.E).smul_mem b (hv j trivial)
      rw [hb]
      simpa [Algebra.smul_def] using h1
    exact this

end GlobalTheory.FunObj.StdDatum.LiftCoset

namespace GlobalTheory.FunObj.StdDatum.LiftCoset

theorem unitBlock_mul_int (D : D7) {a d : ℕ} (r : GA D a) (hr : r ∈ intG D a) (i : Fin d) (j : Fin a) :
    ((unitBlock D 0 a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈
      OhE D := by
  rw [Matrix.mul_apply]
  refine sum_mem fun l _ => mul_mem ?_ ?_
  · rw [Matrix.map_apply]
    by_cases h : i.1 = 0 + l.1
    · simp only [unitBlock, Matrix.of_apply, h, if_true, map_one]; exact one_mem _
    · simp only [unitBlock, Matrix.of_apply, h, if_false, map_zero]; exact zero_mem _
  · rw [Subgroup.coe_inv]
    exact ((mem_intG r).1 hr l j).2

theorem om_cosetV_eq : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (r : GA D a), r ∈ intG D a → ∃ x : Matrix (Fin d) (Fin a) D.host.E, pt D (tor0 D ⊤ δ) δ x ∈ (La0 D (tor0 D ⊤ δ) a d) ∧ (∀ i j, (x.map (inc D) - (unitBlock D 0 a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪) ∧ W.Om r 1 (cosetV D δ 𝔪 0 a d e0) = ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x) (W.Om r 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)) := by
  intro D δ hc a d e0 he W 𝔪 h𝔪 r hr
  set T := tor0 D ⊤ δ
  set G := Iop D T (La0 D T a d) (La D T (stdL D a) (skewLat D 𝔪 d)) e0 with hGdef
  set x₀ := unitBlock D 0 a d with hx₀
  have hT := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have he' : e0 ∈ TT D T a d := hT.1 _ _ (GlobalTheory.FunObj.CosetTT.sd_stdL a) (GlobalTheory.FunObj.CosetTT.sd_stdL d) e0 he
  obtain ⟨M, hM, hMx⟩ := GlobalTheory.FunObj.CosetTT.la_skew_nsmul (D := D) ⊤ δ 𝔪 a d
  have hG : G ∈ TT D T a d :=
    GlobalTheory.FunObj.CosetTT.iop_mem_TT hc _ (fun y hy => ⟨M, hM, hMx y hy⟩) he'
  have hF : Wd D T (pt D T δ x₀) G ∈ TT D T a d := hT.2.1 _ _ hG
  obtain ⟨m, hm, hlift⟩ := W.lift r 1 x₀ G hG
  have hN : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  set R : Matrix (Fin a) (Fin a) (AE D) := (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hR
  set Tm : Matrix (Fin d) (Fin a) (AE D) := x₀.map (inc D) * R with hTm
  have hTint : ∀ i j, Tm i j ∈ OhE D := fun i j => unitBlock_mul_int D r hr i j
  choose b w hw hbw using fun i j =>
    GlobalTheory.CongApprox.exists_int_approx D (m * Ideal.absNorm 𝔪) (Nat.mul_pos hm hN) (Tm i j) (hTint i j)
  set x : Matrix (Fin d) (Fin a) D.host.E := Matrix.of fun i j => (b i j : D.host.E) with hxdef
  have hdiff : ∀ i j, (x.map (inc D) - Tm) i j = -(((m * Ideal.absNorm 𝔪 : ℕ) : AE D) * w i j) := by
    intro i j
    rw [Matrix.sub_apply, Matrix.map_apply, hbw i j]
    simp [hxdef]
  have hnat : ∀ k : ℕ, ((k : ℕ) : AE D) ∈ OhE D := fun k => natCast_mem _ k
  refine ⟨x, LiftCoset.globalIntegralMatrix_mem_stdThetaLattice D δ x (fun i j => ⟨b i j, rfl⟩), fun i j => ?_, ?_⟩
  · rw [hdiff i j, Nat.cast_mul, mul_comm ((m : ℕ) : AE D), mul_assoc]
    exact neg_mem (GlobalTheory.BotPairSmall.BlockIdx.absNorm_mul_mem_hatId D 𝔪 (mul_mem (hnat m) (hw i j)))
  · have hclose : CloseTo D ⊤ m (r : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) x₀ x := by
      intro i j
      refine ⟨-(((Ideal.absNorm 𝔪 : ℕ) : AE D) * w i j),
        GlobalTheory.CongApprox.OhE_le_IhE_top D _ (neg_mem (mul_mem (hnat _) (hw i j))), ?_⟩
      have e1 : (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = 1 := by simp
      have e2 : (((r : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = R := by
        rw [hR, Subgroup.coe_inv]
      rw [e1, Matrix.one_mul, e2, ← hTm, hdiff i j, Nat.cast_mul]
      ring
    have hl := hlift x hclose
    show W.Om r 1 (((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ • Wd D T (pt D T δ x₀) G) = _
    rw [W.smul r 1 _ _ hF, hl]

end GlobalTheory.FunObj.StdDatum.LiftCoset

end
end

