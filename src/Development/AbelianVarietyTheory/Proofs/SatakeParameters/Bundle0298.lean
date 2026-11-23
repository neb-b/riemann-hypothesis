module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0290
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFramesReadSplitPlaceUnitaryGroup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitFrameRead

theorem tensCast_one_tmul {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) (x : E) :
    GlobalTheory.NJoin.tensCast h ((1 : FiniteAdeleRing (𝓞 F1) F1) ⊗ₜ[F1] x) = x ⊗ₜ[F2] (1 : FiniteAdeleRing (𝓞 F2) F2) := by
  subst h; rfl

theorem gen_supp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (fin : A →+* B) (Ψ : B →+* C) {m k : ℕ}
    (M : Matrix (Fin m) (Fin m) A) (β : Matrix (Fin m) (Fin k) B) (K : Matrix (Fin k) (Fin k) B) (β' : Matrix (Fin k) (Fin m) B)
    (h1 : β * β' = 1) (hM : M.map fin = β * K * β') (hK : K.map Ψ = 1) : ((M - 1).map fin).map Ψ = 0 := by
  rw [Matrix.map_sub _ (map_sub _), hM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_sub _ (map_sub _),
    Matrix.map_mul, Matrix.map_mul, hK, Matrix.mul_one, ← Matrix.map_mul, h1, sub_self]


set_option maxHeartbeats 1000000 in
theorem side_loc (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E))
    (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E)
    (hπ : ∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a))))
    (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hV : GlobalTheory.NJoin.StdFrame hF PV) :
    ∃ FS : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) V.rank (Fin n), ∀ h, TrivOutside {s.v} h →
      p.IsLoc FS (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) := by
  obtain ⟨⟨β, β', h1, h2, hm⟩, -⟩ := hV
  let Φ := c.toRingHom.comp (s.proj.comp (GlobalTheory.NJoin.tensCast hF).toRingHom)
  refine ⟨⟨β.map Φ, β'.map Φ, ?_, ?_⟩, fun h hh => ⟨?_, ?_⟩⟩
  · rw [← Matrix.map_mul, h1]; exact Matrix.map_one _ (map_zero Φ) (map_one Φ)
  · rw [← Matrix.map_mul, h2]; exact Matrix.map_one _ (map_zero Φ) (map_one Φ)
  · intro i j
    apply _root_.GlobalTheory.PlaceSupp.idem_mul_eq_self D s hF p c hπ
    · have hk := MonoidHom.mem_ker.1 (PV.into h)
      have e2 : ((Formalism.L2.Theta.mt V (PV.ψ h)) - 1).map (Formalism.L2.Theta.infPart D) = 0 := by
        rw [Matrix.map_sub _ (map_sub (Formalism.L2.Theta.infPart D)),
          Matrix.map_one _ (map_zero (Formalism.L2.Theta.infPart D)) (map_one (Formalism.L2.Theta.infPart D))]
        have e3 : (Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.infPart D) = (Formalism.L2.Theta.infHom V (PV.ψ h)).val := rfl
        rw [e3, hk, Units.val_one, sub_self]
      exact congrFun (congrFun e2 i) j
    · intro v' hv'
      have hh' := hh v' (by simpa using hv')
      have e4 := gen_supp (Formalism.L2.Theta.finPart D) ((ReciprocityTheory.Aut.compAt D.host.E v').comp (GlobalTheory.NJoin.tensCast hF).toRingHom)
        (Formalism.L2.Theta.mt V (PV.ψ h)) β _ β' h1 (hm h) (by
          rw [← hh']
          ext a b
          exact congrArg (ReciprocityTheory.Aut.compAt D.host.E v') (RingEquiv.apply_symm_apply _ _))
      exact congrFun (congrFun e4 i) j
  · have e7 : (Formalism.L2.Theta.mt V (PV.ψ h)).map p.π = ((Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.finPart D)).map Φ :=
      Matrix.ext fun a b => hπ _
    have e5 : (Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.finPart D) = _ := hm h
    have hK : ((h.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm).map Φ =
        (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)).val := by
      refine Matrix.ext fun a b => ?_
      exact congrArg (fun y => c (s.proj y)) (RingEquiv.apply_symm_apply _ _)
    rw [e7, e5, ← hK]
    exact (Matrix.map_mul).trans (congrArg (· * β'.map Φ) Matrix.map_mul)

theorem main : ∀ (D : D7) (V W : Formalism.BasicNotions.TH.HSp D) (n r : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (PW : Formalism.IndefR.principalLevelFrame.RowPsi W r) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.NJoin.StdFrame hF PV → GlobalTheory.NJoin.StdFrame hF PW → ∀ (s : SplitPlace D.host.E), ∃ (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)), Formalism.L2.JoinChr.IsPlIdem D p.e s.w ∧ (∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧ ∃ (FS : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) V.rank (Fin n)) (FT : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) W.rank (Fin r)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), Continuous c ∧ (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧ (∀ h, TrivOutside {s.v} h → p.IsLoc FS (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h))) ∧ ∀ g, TrivOutside {s.v} g → p.IsLoc FT (PW.ψ g) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g)) := by
  intro D V W n r PV PW hF hV hW s
  obtain ⟨p, c, hId, hc, hci, hπ⟩ := _root_.GlobalTheory.SplitLocPlace.exists_place D s hF
  have hpr : ∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x := by
    intro x
    unfold GlobalTheory.LocMod.Place.pr
    rw [hπ]
    have e1 : Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x) =
        (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x := by
      simp [Formalism.L2.Theta.finPart, Formalism.L2.Theta.incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
    rw [e1, tensCast_one_tmul, ← hci x]
    congr 1
    simp [ReciprocityTheory.Aut.SplitPlace.proj]
  obtain ⟨FS, hFS⟩ := side_loc D s hF p c hπ V n PV hV
  obtain ⟨FT, hFT⟩ := side_loc D s hF p c hπ W r PW hW
  exact ⟨p, hId, hpr, FS, FT, c, hc, hci, hFS, hFT⟩

end GlobalTheory.SplitFrameRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionMemSpanLocalSchrodingerModelsSplit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel
namespace GlobalTheory.LocMod.SpanModels

theorem mem_iSup_range_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : Formalism.BasicNotions.TH.HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ f, Formalism.IndefR.Datum.IsThetaFunO ψ S T f → f ∈ ⨆ (Tm : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) →ₗ[ℂ] (Formalism.IndefR.Datum.WO S T → ℂ)) (_ : p.IsModel ψ FS FT Tm), LinearMap.range Tm := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ f hf
  classical
  obtain ⟨U, hUo, hUf⟩ := hf.level
  obtain ⟨c, hc, L', K, hL, hL'e, hK, ⟨R, hR⟩, hL'K, hsep⟩ := _root_.GlobalTheory.LatChoiceSplit.exists_split_lattices D k p Y Y' S T FS FT ψ hψ U hUo
  have hinf : Formalism.L2.Theta.infPart D p.e = 0 := GlobalTheory.PlaceCoord.infPart_split p.split
  have hinf' : Formalism.L2.Theta.infPart D (Formalism.L2.Theta.cA D p.e) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hec : p.e * Formalism.L2.Theta.cA D p.e = 0 := p.split.2.1
  let I : AddSubgroup (Matrix Y Y' k) :=
    { carrier := {x | ∀ i j, x i j ∈ 𝒪[k]}
      add_mem' := fun ha hb i j => add_mem (ha i j) (hb i j)
      zero_mem' := fun i j => zero_mem _
      neg_mem' := fun ha i j => neg_mem (ha i j) }
  let L : AddSubgroup (Formalism.IndefR.Datum.WO S T) :=
    I.map ((Witness.upH p FS FT).comp (DistribSMul.toAddMonoidHom (Matrix Y Y' k) c))
  have memL : ∀ t, t ∈ L ↔ ∃ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) ∧ p.up FS FT (c • x) = t := fun t => Iff.rfl
  let W : Submodule ℂ (Formalism.IndefR.Datum.WO S T → ℂ) :=
    { carrier := {g | Formalism.IndefR.Datum.IsThetaFunO ψ S T g}
      add_mem' := fun ha hb => GlobalTheory.LocMod.LinSpace.isThetaFunO_add ha hb
      zero_mem' := GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ S T
      smul_mem' := fun c _ hg => GlobalTheory.LocMod.LinSpace.isThetaFunO_smul c hg }
  have key := GlobalTheory.T.mem_span_translates_of_fixed_lattice (fun x y => ψ (Formalism.IndefR.Datum.symplO S T x y)) (isBichar_symplO S T ψ) (heisL S T ψ)
    (half S T p.e) (half S T (Formalism.L2.Theta.cA D p.e)) L L' K
    (by rintro _ ⟨x, hx, rfl⟩; exact (hL x hx).1)
    (fun t ht => (isHalf_iff S T).1 (hL'e t ht))
    (fun y hy => (isHalf_iff S T).1 (hK y hy).1)
    (fun v => by
      funext w
      change ψ (Formalism.IndefR.Datum.symplOH S T w 0) * v (w + 0) = v w
      simp [Formalism.IndefR.Datum.symplOH, symplO_zero_right])
    (fun x hx x' hx' v => heisL_half S T ψ (by rw [mul_comm]; exact hec) x hx x' hx' v)
    (fun y hy y' hy' v => heisL_half S T ψ (by rw [Formalism.L2.Theta.cA_cA, hec]) y hy y' hy' v)
    (fun x _ y _ v => heisL_comm S T ψ x y v)
    ⟨R, fun t ht => by
      obtain ⟨r, hr, x, hx, e⟩ := hR t ht
      exact ⟨r, hr, x, hx, e.symm⟩⟩
    hL'K (fun y hy h => hsep y ((isHalf_iff S T).2 hy) h) W
    (fun v hv x _ => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hv x)
    (fun v hv y _ => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hv y)
    f hf
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact hUf _ (hL x hx).2 (GlobalTheory.PlaceDatum.infPart_of_half hinf (Witness.up_half p FS FT _)))
    (fun y hy => hUf y (hK y hy).2 (GlobalTheory.PlaceDatum.infPart_of_half hinf' (hK y hy).1))
  refine Submodule.span_le.2 ?_ key
  rintro _ ⟨r, hr, g, hg, hgL, hgY, rfl⟩
  exact _root_.GlobalTheory.LocMod.Place.heisO_mem_iSup_range_of_fixed D k p Y Y' S T FS FT ψ hψ c hc g hg (fun x hx => hgL _ ⟨x, hx, rfl⟩)
    (fun y hy hyL => hgY y ((isHalf_iff S T).1 hy) (by rintro _ ⟨x, hx, rfl⟩; exact hyL x hx)) r ((isHalf_iff S T).2 hr)

end GlobalTheory.LocMod.SpanModels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftSpacesRankConstAndLocalisationScalars
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RankTw

open GlobalTheory.RowCopy GlobalTheory.NRows

theorem used_loc (D : D7) (i : D.nd.Loc) : D.nd.mu i = D.what₂.mu0 ∨ ∃ w, D.nd.mu i = D.what₂.muAt w :=
  Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩

theorem lamPos_of_used {D : D7} (h : LamUsed D) {μ} (hμ : μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : LamPos D μ j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact h μ hμ ⟨k, by omega⟩

theorem lamLoc {D : D7} (h : LamUsed D) (i : D.nd.Loc) : LamPos D (D.nd.mu i) (D.nd.j i) :=
  lamPos_of_used h (used_loc D i) (D.nd.j_range i).1 (D.nd.j_range i).2

theorem up_injective {D : D7} {μ} {j : ℕ} (h : LamPos D μ j) (hI : DirectSum.IsInternal (D.what₂.isot j)) :
    Function.Injective (D.what₂.thetaT μ j) := by
  have hs : Function.Surjective (D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hI.submodule_iSup_eq_top, iSup_le_iff]
    intro σ f hf
    by_cases h0 : D.what₂.isot j σ = ⊥
    · rw [h0] at hf
      rw [(Submodule.mem_bot ℂ).1 hf]
      exact zero_mem _
    · have hl : ((D.what₂.lamP μ j σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ((h σ).2 h0).ne'
      refine ⟨((D.what₂.lamP μ j σ : ℝ) : ℂ)⁻¹ • f, ?_⟩
      rw [map_smul, LinearMap.comp_apply, (h σ).1 f hf, smul_smul, inv_mul_cancel₀ hl, one_smul]
  have hi := LinearMap.injective_iff_surjective.2 hs
  rw [LinearMap.coe_comp] at hi
  exact hi.of_comp

theorem rank_of {D : D7} (hI : SumRepresentations.adm8 D) (h : LamUsed D) (L : SizeData₂ D) : TwistedPlaces.adm3 L := by
  intro j hj w hw
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  have e : D.what₂.muTw w = D.what₂.muAt w := ((D.what₂.muAt_or w).resolve_left hw).symm
  have a := up_injective (lamPos_of_used h (Or.inr ⟨w, e⟩) h1 h2) (hI j h1 h2)
  have b := up_injective (lamPos_of_used h (Or.inl rfl) h1 h2) (hI j h1 h2)
  unfold SizeData₂.zeroSpaceRankAtPlace SizeData₂.dZ0 Rows.Data.Zj
  rw [LinearMap.finrank_range_of_inj a, LinearMap.finrank_range_of_inj b]

theorem main : ∀ D : D7, Formalism.MainNotions.SumRepresentations.adm8 D → GlobalTheory.NRows.LamUsed D →
    (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) ∧ ∀ L : SizeData₂ D, Formalism.MainNotions.TwistedPlaces.adm3 L :=
  fun _ hI h => ⟨GlobalTheory.RankTw.lamLoc h, GlobalTheory.RankTw.rank_of hI h⟩

end GlobalTheory.RankTw

end
end

