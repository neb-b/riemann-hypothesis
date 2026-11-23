module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ZeroEigensystemNotPassageOfFiniteType
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeThetaLevel3Exists
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem tw_cut_eig (s : Bool) {E I C : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (h : I → Module.End ℂ E) (e : Module.End ℂ E) (Ec : C → Submodule ℂ E) (lab : C → I → ℂ)
    (he : e * e = e) (hs : (⨆ c, Ec c) = LinearMap.range e) (hl : ∀ c, ∀ w ∈ Ec c, ∀ i, h i w = lab c i • w) :
    Formalism.L2.Col.PairComm (fun i => (Tw.map s (h i * e) : Module.End ℂ (Tw s E))) ∧
      ∀ Q : (I → ℂ) → Prop, ¬ Q 0 →
        Formalism.L2.Col.eigSum (fun i => (Tw.map s (h i * e) : Module.End ℂ (Tw s E))) Q =
          Tw.sub s (⨆ (c : C) (_ : Q (fun i => cj s (lab c i))), Ec c) := by
  obtain ⟨hc, hq⟩ := GlobalTheory.Hk3.eigSum_mul_proj_eq h e Ec lab he hs hl
  obtain ⟨a, b, -⟩ := _root_.GlobalTheory.TwEig.pairComm_eigSum_sub_iSup s (fun i => h i * e)
  refine ⟨a hc, fun Q hQ => ?_⟩
  have h0 : (fun i => cj s ((0 : I → ℂ) i)) = 0 := by funext i; simp
  rw [b Q, hq _ (by rw [h0]; exact hQ)]

theorem cxSys_cj_iff {K I : Type} [Field K] {σ τ : K →+* ℂ} {s : Bool} (h : ∀ a, σ a = cj s (τ a)) (H : (I → K) → Prop) (y : I → ℂ) :
    cxSys σ H (fun i => cj s (y i)) ↔ cxSys τ H y := by
  constructor
  · rintro ⟨x, hx, e⟩
    refine ⟨x, hx, funext fun i => ?_⟩
    have := congrFun e i
    simp only [h] at this
    simpa [cj_cj] using congrArg (cj s) this
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, funext fun i => (h _).symm⟩

set_option maxHeartbeats 2000000 in
theorem heckeTheta_level3_exists_alt : HoweUnram → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → (R.toCx3 F).PartsW false → A3.fam3.TypesSep3 → ((∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → ∃ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW := by
  intro hHowe hHC hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hLI hC hEx hJ s hOk hGG hLU hGU hGE hLW hA hPos hB hParts hTS hPin
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨hCoreE, hSF, -, -, -, hWc, -⟩ := _root_.GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC
  have hCore := hCoreE hEx
  have hSch : SchurAll R.toRealDat :=
    ⟨fun _ _ _ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hHC hCusp D _ _ _ _ _ _ _ _).2,
      (GlobalTheory.MultFinite.hcFinite_and_schurMult hHC hCusp D _ _ _ _ _ _ _ _).2,
      fun _ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hHC hCusp D _ _ _ _ _ _ _ _).2⟩
  have hTr := (hPin (_root_.GlobalTheory.TrPass.exists_inert_passage hHowe R F hLI hC hEx hSch hJ hirr hB hPos)).1
  have hOps := fun i => _root_.GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R.toRealDat F.lv2 hCore hSch hirr R.SF hSF i
  choose h hIsW hNorm hGc hSup hInv hEig hChar using hOps
  have hDict := _root_.GlobalTheory.LiftDictionary.every_op_label hHowe R F hLI hC hEx hSch hJ
  choose pl cV cW hD using hDict
  have hLaws := GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hCore hirr
  have hcut := fun j => tw_cut_eig (twAt D.what₂.embLL A3.A.v0) (fun i => h j (pl j A3.A.μ0 i) (cW j A3.A.μ0 i)) (eH R.toRealDat j)
    (Wcc R.toRealDat R.SF j) (fun c => labW j (pl j A3.A.μ0) (cW j A3.A.μ0) c) (hLaws j).1 (hSup j)
    (fun c w hw i => hEig j c _ ((hD j A3.A.μ0).good i) _ w hw)
  refine ⟨fun j t i => Tw.map (E := (R.HW j (sg0 D A3.A)).H) (F := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) (h j (pl j t i) (cW j t i) * eH R.toRealDat j), ?_, ?_, ?_⟩
  · intro j t i u
    obtain ⟨hV, hVo, -⟩ := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hCore.lev hCore.fam hCore.models).2 j t
    have hK := RealDat3.kFormL_of (R := R) (F := F) hCore.models
    have hop : (R.toCx3 F).opLC j t (Sum.inl i) = Tw.map (E := (R.HV j t).H) (F := (R.HV j t).H) (twAt D.what₂.embLL A3.A.v0) (hV (pl j t i) (cV j t i)) := by
      refine LinearMap.ext_on_range (hK j t).2 fun k => ?_
      rw [← CxData.jL_opL _ hK]
      show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.jV j t ((A3.liftI j t).opAll i _)) = Tw.mk (twAt D.what₂.embLL A3.A.v0) (hV _ _ (R.jV j t _))
      exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) ((hD j t).op hV hVo i _)
    have hs := (_root_.GlobalTheory.SysW.matched_operators_theta_intertwine R.toRealDat F.lv2 hCore hSch hirr R.SF hSF j t (pl j t i) ((hD j t).good i) _ _ ((hD j t).mat i) hV hVo).1 (h j) (hIsW j)
    rw [hop]
    show R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (hV _ _ (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u))) =
      Tw.map (E := (R.HW j (sg0 D A3.A)).H) (F := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) (h j (pl j t i) (cW j t i) * eH R.toRealDat j)
        (R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u)))
    rw [map_smul]
    congr 1
    show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (hV _ _ (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u))) = Tw.mk (twAt D.what₂.embLL A3.A.v0) (h j (pl j t i) (cW j t i) (eH R.toRealDat j (R.thG j t (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u))))
    rw [(hLaws j).2.2.2 t, hs]
  · intro j
    exact (hcut j).1
  · intro j p
    have hv := fun a => R.toRealDat.emb0 a
    have hQ0 : ¬ cxSys A3.fam3.base3.v0.embedding ((A3.liftI j A3.A.fam.μ0).HasRes3 (A3.fam3.tr3 j p.1)) 0 := by
      intro h0
      have h1 : (0 : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) = fun i => cj (twAt D.what₂.embLL A3.A.v0) ((0 : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) i) := by
        funext i; simp
      rw [h1] at h0
      exact _root_.GlobalTheory.ZeroPassage.zero_not_passage R F hC j p ((cxSys_cj_iff hv _ _).1 h0)
    have key := (hcut j).2 _ hQ0
    show Tw.sub _ (R.Wp3 j p) = _
    refine Eq.trans ?_ key.symm
    congr 1
    apply le_antisymm
    · refine iSup₂_le fun c hc => ?_
      by_cases hne : R.Wc' j c = ⊥
      · rw [hne]; exact bot_le
      · exact le_iSup₂_of_le c ((cxSys_cj_iff hv _ _).2
          (_root_.GlobalTheory.Hk3.passage_of_carried hHowe R F hLI hC hEx hSch hJ s hOk hGG hLU hGU hGE hLW hA hPos hB hTr j _ _ _ (hD j A3.A.μ0) p c hc hne)) (hWc j c).le
    · refine iSup₂_le fun c hc => ?_
      rw [← hWc j c]
      exact _root_.GlobalTheory.Hk3.Back.wc_le_wp_of_passage hHowe R F hLI hC hEx hSch hJ s hOk hGG hLU hGU hGE hLW hA hPos hB hTr hParts hTS j _ _ _ (hD j A3.A.μ0) p c
        ((cxSys_cj_iff hv _ _).1 hc)

end GlobalTheory.Hk3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalMemUnitaryGroupAntidiagonal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem unitary_conj_by_inverse_pair_preserves_form {K : Type} [CommRing K] (σ : K →+* K) {n : ℕ}
    (P Q M J : Matrix (Fin n) (Fin n) K) (hPQ : P * Q = 1) (hM2 : Formalism.UG.cT σ M * M = 1)
    (hJ : Formalism.UG.cT σ P * P = J) : Formalism.UG.cT σ (Q * M * P) * J * (Q * M * P) = J := by
  have hQP : Formalism.UG.cT σ Q * Formalism.UG.cT σ P = 1 := by rw [← Formalism.UG.cT_mul, hPQ, Formalism.UG.cT_one]
  subst hJ
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]
  calc _ = Formalism.UG.cT σ P * Formalism.UG.cT σ M * (Formalism.UG.cT σ Q * Formalism.UG.cT σ P) * (P * Q) * M * P := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ P * P := by
        rw [hQP, hPQ, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc (Formalism.UG.cT σ P), hM2, Matrix.mul_one]

open Formalism.UG in
theorem inertLoc_mem_GU (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x ∈ Formalism.UG.GU Dv.σw n := by

  have hcomm : ∀ a : AL L, compAt L v (conjAL L a) =
      Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L))
        (compAt L v a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [compAt, conjAL, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  set f : AL L →+* w.adicCompletion L := (Dv.e : _ →+* w.adicCompletion L).comp (compAt L v) with hf
  have hfc : ∀ a, f (conjAL L a) = Dv.σw (f a) := by
    intro a; simp only [hf, RingHom.comp_apply, hcomm]; exact Dv.comm _
  set A : Matrix (Fin n) (Fin n) (AL L) := ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hA
  have hx : A * conjT (conjAL L) A = 1 := x.2
  set M : Matrix (Fin n) (Fin n) (w.adicCompletion L) := A.map f with hM
  have hMc : (conjT (conjAL L) A).map f = cT Dv.σw M := by
    ext i j; simp [conjT, cT, hM, hfc]
  have hM1 : M * cT Dv.σw M = 1 := by
    rw [← hMc, hM, ← Matrix.map_mul, hx, Matrix.map_one f (map_zero f) (map_one f)]
  have hM2 : cT Dv.σw M * M = 1 := mul_eq_one_comm.mp hM1
  have hloc : ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * M *
        (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) := by
    simp only [Formalism.AUTREP.InertDatum.loc, Units.val_mul, hM, hA, hf]
    congr 2
  have hPQ : (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key := unitary_conj_by_inverse_pair_preserves_form Dv.σw _ _ M _ hPQ hM2 Dv.Panti
  rw [← hloc] at key
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDoubleCosetOperatorEqInertHeckeOperator
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertDCOp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

theorem loc_mul (Dv : InertDatum L n v w) (x y : GAf L n) : Dv.loc (x * y) = Dv.loc x * Dv.loc y :=
  (GlobalTheory.SatInd.CosetFin.locHom Dv).map_mul x y

theorem mem_dc_iff (Dv : InertDatum L n v w) (h1 : ∀ x : GAf L n, Dv.loc x ∈ Formalism.UG.GU Dv.σw n)
    (h2 : ∀ κ : GAf L n, κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
      (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n)
    (h3 : ∀ k : GL (Fin n) (w.adicCompletion L), k ∈ Formalism.UG.GU Dv.σw n →
      ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = k)
    (h4 : ∀ x y : GAf L n, TrivOutside {v} x → TrivOutside {v} y → Dv.loc x = Dv.loc y → x = y)
    {a x : GAf L n} (ha : TrivOutside {v} a) (hx : TrivOutside {v} x) :
    (⟨Dv.loc x, h1 x⟩ : Formalism.UG.GU Dv.σw n) ∈ DoubleCoset.doubleCoset (⟨Dv.loc a, h1 a⟩ : Formalism.UG.GU Dv.σw n)
        (Formalism.UG.KU Dv.σw n : Set (Formalism.UG.GU Dv.σw n)) (Formalism.UG.KU Dv.σw n : Set (Formalism.UG.GU Dv.σw n)) ↔
      ∃ k₁ ∈ InertSph.Kv L n v, ∃ k₂ ∈ InertSph.Kv L n v, x = k₁ * a * k₂ := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨k₁, hk₁, k₂, hk₂, e⟩
    obtain ⟨κ₁, t₁, e₁⟩ := h3 k₁.1 k₁.2
    obtain ⟨κ₂, t₂, e₂⟩ := h3 k₂.1 k₂.2
    have u₁ : κ₁ ∈ Umax L n := GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv κ₁ t₁
      (fun i j => by rw [e₁]; exact GlobalTheory.SatInd.CosetFin.entries_int hk₁ i j)
    have u₂ : κ₂ ∈ Umax L n := GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv κ₂ t₂
      (fun i j => by rw [e₂]; exact GlobalTheory.SatInd.CosetFin.entries_int hk₂ i j)
    refine ⟨κ₁, ⟨u₁, t₁⟩, κ₂, ⟨u₂, t₂⟩, h4 _ _ hx
      (GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul t₁ ha) t₂) ?_⟩
    calc Dv.loc x = k₁.1 * Dv.loc a * k₂.1 := congrArg Subtype.val e
      _ = Dv.loc κ₁ * Dv.loc a * Dv.loc κ₂ := by rw [e₁, e₂]
      _ = Dv.loc (κ₁ * a * κ₂) := by rw [loc_mul, loc_mul]
  · rintro ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    refine ⟨⟨Dv.loc k₁, h1 k₁⟩, h2 k₁ hk₁.1 (h1 k₁), ⟨Dv.loc k₂, h1 k₂⟩,
      h2 k₂ hk₂.1 (h1 k₂), ?_⟩
    apply Subtype.ext
    show Dv.loc (k₁ * a * k₂) = Dv.loc k₁ * Dv.loc a * Dv.loc k₂
    rw [loc_mul, loc_mul]

end GlobalTheory.InertDCOp

namespace GlobalTheory.InertDCOp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

theorem exists_reps (Dv : InertDatum L n v w) (h1 : ∀ x : GAf L n, Dv.loc x ∈ Formalism.UG.GU Dv.σw n)
    (h2 : ∀ κ : GAf L n, κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
      (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n)
    {a : GAf L n} (ha : TrivOutside {v} a) :
    ∃ R : Finset (GAf L n), GlobalTheory.SphLabelOps.Reps (InertSph.Kv L n v) a R := by
  classical
  set K := InertSph.Kv L n v
  let p : GAf L n → Prop := fun x => ∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂
  have tp : ∀ x, p x → TrivOutside {v} x := by
    rintro _ ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    exact GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul hk₁.2 ha) hk₂.2
  have hfin : Set.Finite {c : GAf L n ⧸ K | ∃ x : GAf L n, (x : GAf L n ⧸ K) = c ∧ p x} := by
    refine GlobalTheory.SatInd.CosetFin.finite_cosets (GlobalTheory.SatInd.CosetFin.locHom Dv) (Formalism.UG.GU Dv.σw n)
      (Formalism.UG.KU Dv.σw n) K p _
      (GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram ⟨Dv.loc a, h1 a⟩) ?_ ?_
    · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
      refine ⟨h1 _, ⟨Dv.loc k₁, h1 k₁⟩, h2 k₁ hk₁.1 (h1 k₁), ?_⟩
      have e : (⟨GlobalTheory.SatInd.CosetFin.locHom Dv (k₁ * a * k₂), h1 _⟩ : Formalism.UG.GU Dv.σw n) =
          (⟨Dv.loc k₁, h1 k₁⟩ * ⟨Dv.loc a, h1 a⟩ : Formalism.UG.GU Dv.σw n) * ⟨Dv.loc k₂, h1 k₂⟩ := by
        apply Subtype.ext
        show Dv.loc (k₁ * a * k₂) = Dv.loc k₁ * Dv.loc a * Dv.loc k₂
        rw [loc_mul, loc_mul]
      rw [e]
      exact (QuotientGroup.mk_mul_of_mem _ (h2 k₂ hk₂.1 (h1 k₂))).symm
    · intro x y hx hy hz hk
      have ht : TrivOutside {v} (x⁻¹ * y) :=
        GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv (tp x hx)) (tp y hy)
      exact ⟨GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv _ ht
        (fun i j => GlobalTheory.SatInd.CosetFin.entries_int hk i j), ht⟩
  refine ⟨hfin.toFinset.image (fun c => c.out), ?_, ?_⟩
  · intro γ hγ
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨x, hxc, k₁, hk₁, k₂, hk₂, rfl⟩ := (Set.Finite.mem_toFinset hfin).1 hc
    have hm : (k₁ * a * k₂)⁻¹ * c.out ∈ K := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', hxc]
    exact ⟨k₁, hk₁, k₂ * ((k₁ * a * k₂)⁻¹ * c.out), mul_mem hk₂ hm, by group⟩
  · intro x hx
    have hc : (x : GAf L n ⧸ K) ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).2 ⟨x, rfl, hx⟩
    refine ⟨(x : GAf L n ⧸ K).out, ⟨Finset.mem_image_of_mem _ hc, ?_⟩, ?_⟩
    · rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    · rintro γ ⟨hγ, hγx⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hγ
      have : c = (x : GAf L n ⧸ K) := by
        rw [← QuotientGroup.out_eq' c]
        exact QuotientGroup.eq.2 hγx
      rw [this]

end GlobalTheory.InertDCOp

namespace GlobalTheory.InertDCOp

theorem dcOp_eq_heckeFunI : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ x : GAf L n, Dv.loc x ∈ Formalism.UG.GU Dv.σw n) → (∀ κ : GAf L n, κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n) → (∀ k : GL (Fin n) (w.adicCompletion L), k ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = k) → (∀ x y : GAf L n, TrivOutside {v} x → TrivOutside {v} y → Dv.loc x = Dv.loc y → x = y) → ∀ a : GAf L n, TrivOutside {v} a → ∃ (R : Finset (GAf L n)) (ha : Formalism.UG.GU Dv.σw n → ℂ), GlobalTheory.SphLabelOps.Reps (GlobalTheory.InertSph.Kv L n v) a R ∧ ha ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W), (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → ∑ γ ∈ R, NG.rt L n γ φ = heckeFunI L n (Umax L n) Dv ha φ := by
  intro L _ _ _ n v w Dv h1 h2 h3 h4 a ha
  classical
  set K := InertSph.Kv L n v
  obtain ⟨R, hR⟩ := exists_reps Dv h1 h2 ha
  have tR : ∀ γ ∈ R, TrivOutside {v} γ := by
    intro γ hγ
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hR.1 γ hγ
    exact GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul hk₁.2 ha) hk₂.2
  refine ⟨R, Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩, hR,
    Formalism.UG.P.double_coset_indicator_mem _ _ _ _, fun W _ _ φ hφ => ?_⟩

  have hv1 : ∀ x : GAf L n, TrivOutside {v} x → (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂) →
      Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩) (Dv.loc x) = 1 := by
    intro x hx hp
    unfold Formalism.AUTREP.InertDatum.hval
    rw [dite_eq_left (h1 x)]
    exact Formalism.UG.P.dosetInd_of_mem ℂ _ _ _ ((mem_dc_iff Dv h1 h2 h3 h4 ha hx).2 hp)
  have hv0 : ∀ x : GAf L n, TrivOutside {v} x →
      Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩) (Dv.loc x) ≠ 0 →
      ∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂ := by
    intro x hx h0
    unfold Formalism.AUTREP.InertDatum.hval at h0
    rw [dite_eq_left (h1 x)] at h0
    refine (mem_dc_iff Dv h1 h2 h3 h4 ha hx).1 ?_
    by_contra hn
    exact h0 (Formalism.UG.P.dosetInd_of_not_mem ℂ _ _ _ hn)
  funext g
  rw [Finset.sum_apply]
  unfold heckeFunI
  rw [finsum_eq_sum_of_support_subset (s := R.image (QuotientGroup.mk : GAf L n → GAf L n ⧸ Umax L n))]
  · rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun γ hγ => ?_
      have hc : ∃ x : GAf L n, (x : GAf L n ⧸ Umax L n) = (γ : GAf L n ⧸ Umax L n) ∧ TrivOutside {v} x :=
        ⟨γ, rfl, tR γ hγ⟩
      rw [dite_eq_left hc]
      obtain ⟨e, hxt⟩ := hc.choose_spec
      have hU : γ⁻¹ * hc.choose ∈ Umax L n := QuotientGroup.eq.1 e.symm
      have hT : TrivOutside {v} (γ⁻¹ * hc.choose) :=
        GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv (tR γ hγ)) hxt
      have hp : ∃ k₁ ∈ K, ∃ k₂ ∈ K, hc.choose = k₁ * a * k₂ := by
        obtain ⟨k₁, hk₁, k₂, hk₂, e'⟩ := hR.1 γ hγ
        exact ⟨k₁, hk₁, k₂ * (γ⁻¹ * hc.choose), mul_mem hk₂ ⟨hU, hT⟩, by rw [← mul_assoc, ← e']; group⟩
      rw [hv1 _ hxt hp, one_smul]
      have := congrFun (hφ _ hU hT) (g * γ)
      show φ (g * γ) = φ (g * hc.choose)
      rw [← this]
      show φ (g * γ * (γ⁻¹ * hc.choose)) = φ (g * hc.choose)
      group
    · intro γ hγ γ' hγ' e
      have hU : γ⁻¹ * γ' ∈ Umax L n := QuotientGroup.eq.1 e
      have hT : TrivOutside {v} (γ⁻¹ * γ') :=
        GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv (tR γ hγ)) (tR γ' hγ')
      exact (hR.2 γ' (hR.1 γ' hγ')).unique ⟨hγ, hU, hT⟩ ⟨hγ', by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro c hc0
    rw [Function.mem_support] at hc0
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ Umax L n) = c ∧ TrivOutside {v} x
    · rw [dite_eq_left hc] at hc0
      obtain ⟨e, hxt⟩ := hc.choose_spec
      have h0 : Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩) (Dv.loc hc.choose) ≠ 0 := by
        intro h0; rw [h0, zero_smul] at hc0; exact hc0 rfl
      obtain ⟨γ, ⟨hγ, hγx⟩, -⟩ := hR.2 _ (hv0 _ hxt h0)
      rw [Finset.coe_image]
      refine ⟨γ, hγ, ?_⟩
      show (γ : GAf L n ⧸ Umax L n) = c
      rw [← e]
      exact QuotientGroup.eq.2 hγx.1
    · exact absurd (dif_neg hc) hc0

end GlobalTheory.InertDCOp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorLevelIndependent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertLevel


open Classical in
theorem finsum_cosets_eq {G W : Type} [Group G] [AddCommMonoid W] (S K U : Subgroup G)
    (hU : ∀ κ ∈ S, (κ ∈ U ↔ κ ∈ K)) (F : G → W)
    (hF : ∀ x ∈ S, ∀ κ ∈ S, κ ∈ K → F (x * κ) = F x) :
    (∑ᶠ c : G ⧸ U, if hc : ∃ x : G, (x : G ⧸ U) = c ∧ x ∈ S then F hc.choose else 0) =
      ∑ᶠ q : S ⧸ (K.subgroupOf S), F ((q.out : S) : G) := by

  have key : ∀ x y : G, x ∈ S → y ∈ S → (x⁻¹ * y ∈ U ↔ x⁻¹ * y ∈ K) := fun x y hx hy =>
    hU _ (S.mul_mem (S.inv_mem hx) hy)
  let ι : S ⧸ (K.subgroupOf S) → G ⧸ U := fun q => (((q.out : S) : G) : G ⧸ U)
  have hinj : Function.Injective ι := by
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf]
    have h1 := QuotientGroup.eq.1 h
    have h2 := (key _ _ (q.out).2 (q'.out).2).1 h1
    simpa using h2
  have hsupp : (Function.support fun c : G ⧸ U =>
      if hc : ∃ x : G, (x : G ⧸ U) = c ∧ x ∈ S then F hc.choose else 0) ⊆ Set.range ι := by
    intro c hc
    by_cases hc' : ∃ x : G, (x : G ⧸ U) = c ∧ x ∈ S
    · obtain ⟨x, hxc, hxS⟩ := hc'
      refine ⟨((⟨x, hxS⟩ : S) : S ⧸ (K.subgroupOf S)), ?_⟩
      set q : S ⧸ (K.subgroupOf S) := ((⟨x, hxS⟩ : S) : S ⧸ (K.subgroupOf S))
      have h1 := QuotientGroup.eq.1 (QuotientGroup.out_eq' q)
      rw [Subgroup.mem_subgroupOf] at h1
      have h1' : ((q.out : S) : G)⁻¹ * x ∈ K := by simpa using h1
      rw [← hxc]
      exact QuotientGroup.eq.2 ((key _ _ (q.out).2 hxS).2 h1')
    · exact absurd (dif_neg hc') hc
  have hsum := finsum_mem_inter_support (fun c : G ⧸ U =>
      if hc : ∃ x : G, (x : G ⧸ U) = c ∧ x ∈ S then F hc.choose else 0) (Set.range ι)
  rw [Set.inter_eq_right.2 hsupp, finsum_mem_support, finsum_mem_range hinj] at hsum
  rw [hsum]
  refine finsum_congr fun q => ?_
  have hc : ∃ x : G, (x : G ⧸ U) = ι q ∧ x ∈ S := ⟨((q.out : S) : G), rfl, (q.out).2⟩
  rw [dite_eq_left hc]
  obtain ⟨h1, h2⟩ := hc.choose_spec
  have hm : ((q.out : S) : G)⁻¹ * hc.choose ∈ K :=
    (key _ _ (q.out).2 h2).1 (QuotientGroup.eq.1 h1.symm)
  have e : hc.choose = ((q.out : S) : G) * (((q.out : S) : G)⁻¹ * hc.choose) := by group
  rw [e, hF _ (q.out).2 _ (S.mul_mem (S.inv_mem (q.out).2) h2) hm]

end GlobalTheory.InertLevel

namespace GlobalTheory.InertLevel

theorem heckeFunI_level_indep : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ κ : GAf L n, κ ∈ Umax L n → TrivOutside {v} κ → ∃ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n) → ∀ (U U' : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → (∀ κ, TrivOutside {v} κ → (κ ∈ U' ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h : Formalism.UG.GU Dv.σw n → ℂ), Formalism.UG.IsBiInv (Formalism.UG.KU Dv.σw n) h → ∀ φ : GAf L n → W, (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → heckeFunI L n U Dv h φ = heckeFunI L n U' Dv h φ := by
  intro L _ _ _ n v w Dv hKU U U' hU hU' W _ _ h hbi φ hφ
  funext g

  let F : GAf L n → W := fun x => Dv.hval h (Dv.loc x) • φ (g * x)
  have hF : ∀ x ∈ GlobalTheory.InertSph.Gv L n v, ∀ κ ∈ GlobalTheory.InertSph.Gv L n v, κ ∈ Umax L n → F (x * κ) = F x := by
    intro x _ κ hκS hκU
    obtain ⟨hκ, hk⟩ := hKU κ hκU hκS
    have hloc : Dv.loc (x * κ) = Dv.loc x * Dv.loc κ := (GlobalTheory.SatInd.CosetFin.locHom Dv).map_mul x κ
    have hφκ : φ (g * x * κ) = φ (g * x) := congrFun (hφ κ hκU hκS) (g * x)
    have hval : Dv.hval h (Dv.loc x * Dv.loc κ) = Dv.hval h (Dv.loc x) := by
      unfold InertDatum.hval
      by_cases hy : Dv.loc x ∈ Formalism.UG.GU Dv.σw n
      · have hyk : Dv.loc x * Dv.loc κ ∈ Formalism.UG.GU Dv.σw n := (Formalism.UG.GU Dv.σw n).mul_mem hy hκ
        rw [dite_eq_left hyk, dite_eq_left hy]
        have e := hbi 1 ⟨⟨Dv.loc κ, hκ⟩, hk⟩ ⟨Dv.loc x, hy⟩
        simp only [OneMemClass.coe_one, one_mul] at e
        exact e
      · have hyk : Dv.loc x * Dv.loc κ ∉ Formalism.UG.GU Dv.σw n := fun hm => hy (by
          simpa using (Formalism.UG.GU Dv.σw n).mul_mem hm ((Formalism.UG.GU Dv.σw n).inv_mem hκ))
        rw [dif_neg hyk, dif_neg hy]
    show Dv.hval h (Dv.loc (x * κ)) • φ (g * (x * κ)) = Dv.hval h (Dv.loc x) • φ (g * x)
    rw [hloc, hval, ← mul_assoc, hφκ]
  have e1 := finsum_cosets_eq (GlobalTheory.InertSph.Gv L n v) (Umax L n) U (fun κ hκ => hU κ hκ) F hF
  have e2 := finsum_cosets_eq (GlobalTheory.InertSph.Gv L n v) (Umax L n) U' (fun κ hκ => hU' κ hκ) F hF
  exact e1.trans e2.symm

end GlobalTheory.InertLevel
end
end

