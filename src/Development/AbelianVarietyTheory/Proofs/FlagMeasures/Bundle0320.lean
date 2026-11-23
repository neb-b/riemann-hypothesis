module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesSameInnerDifferByRationalUnipotent
public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.AdeleLC
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0089

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesEqOfAdaptedIsometryInnerLatticesEq
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.Unfold.SideEq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem frame_castSucc {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (i : Fin D.R.rS) :
    frame F (Fin.castSucc i) = F.fl.e i := by
  simp [frame, FlagG.fvec]

theorem frame_last {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) :
    frame F (Fin.last D.R.rS) = F.fl.z := by
  simp [frame, FlagG.fvec]

theorem xflag_top {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : Xflag F D.R.rS = Xsp F := by
  simp only [Xflag, Xsp, FlagG.Xa, FlagG.X]
  congr 1
  have : {i : Fin D.R.rS | i.1 < D.R.rS} = Set.univ := by ext i; simp [i.2]
  rw [this, Set.image_univ]

theorem xflag_mono {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {i j : ℕ} (h : i ≤ j) : Xflag F i ≤ Xflag F j := by
  exact Submodule.span_mono (Set.image_mono fun k (hk : k.1 < i) => (lt_of_lt_of_le hk h : k.1 < j))

theorem xflag_eq_range {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (j : ℕ) :
    Xflag F j = Submodule.span D.host.E (Set.range fun i : {i : Fin D.R.rS // i.1 < j} => F.fl.e i.1) := by
  simp only [Xflag, FlagG.Xa]
  congr 1
  ext x; simp

theorem finrank_xflag_eq {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (j : ℕ) :
    Module.finrank D.host.E (Xflag F j) = Fintype.card {i : Fin D.R.rS // i.1 < j} := by
  rw [(LinearEquiv.ofEq _ _ (xflag_eq_range F j)).finrank_eq]
  exact finrank_span_eq_card (F.fl.e_indep.comp (fun i : {i : Fin D.R.rS // i.1 < j} => i.1) Subtype.val_injective)

theorem finrank_xflag {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (G : LFlag (D.sp.Y 0) D.R.rS T') (j : ℕ) :
    Module.finrank D.host.E (Xflag F j) = Module.finrank D.host.E (Xflag G j) := by
  rw [finrank_xflag_eq, finrank_xflag_eq]

theorem map_xflag_le {T : D.host.E} {F G : LFlag (D.sp.Y 0) D.R.rS T} {g : GV D} (hg : Adapt g F G) (j : ℕ) :
    (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag G j := by
  simp only [Xflag, FlagG.Xa]
  rw [Submodule.map_span_le]
  rintro _ ⟨i, hi, rfl⟩
  have h1 := hg.2 (Fin.castSucc i)
  rw [frame_castSucc, frame_castSucc] at h1
  have e : (g : (VS D).V →ₗ[D.host.E] (VS D).V) (F.fl.e i) = (g (F.fl.e i) - G.fl.e i) + G.fl.e i := by
    simp
  rw [e]
  refine add_mem ?_ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hle := xflag_mono G (show (Fin.castSucc i).val ≤ j from le_of_lt hi)
  exact hle h1

theorem map_xflag {T : D.host.E} {F G : LFlag (D.sp.Y 0) D.R.rS T} {g : GV D} (hg : Adapt g F G) (j : ℕ) :
    (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag G j := by
  haveI : FiniteDimensional D.host.E (Xflag G j) :=
    FiniteDimensional.span_of_finite D.host.E ((Set.toFinite _).image _)
  refine Submodule.eq_of_le_of_finrank_eq (map_xflag_le hg j) ?_
  rw [LinearEquiv.finrank_map_eq]
  exact finrank_xflag F G j

theorem map_xsp {T : D.host.E} {F G : LFlag (D.sp.Y 0) D.R.rS T} {g : GV D} (hg : Adapt g F G) :
    (Xsp F).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G := by
  rw [← xflag_top, ← xflag_top]; exact map_xflag hg _

theorem adapt_mul {T : D.host.E} {F G H : LFlag (D.sp.Y 0) D.R.rS T} {g g' : GV D} (hg : Adapt g F G)
    (hg' : Adapt g' G H) : Adapt (g' * g) F H := by
  refine ⟨mul_mem hg'.1 hg.1, fun a => ?_⟩
  have e : (g' * g) (frame F a) - frame H a = g' (g (frame F a) - frame G a) + (g' (frame G a) - frame H a) := by
    change g' (g (frame F a)) - frame H a = _
    rw [map_sub]; abel
  rw [e]
  refine add_mem ?_ (hg'.2 a)
  rw [← map_xflag hg' a.val]
  exact Submodule.mem_map_of_mem (hg.2 a)

theorem adapt_inv {T : D.host.E} {F G : LFlag (D.sp.Y 0) D.R.rS T} {g : GV D} (hg : Adapt g F G) :
    Adapt g⁻¹ G F := by
  refine ⟨inv_mem hg.1, fun a => ?_⟩
  have hm := map_xflag hg a.val
  have h2 := hg.2 a
  rw [← hm] at h2
  obtain ⟨y, hy, hye⟩ := h2
  have e : g⁻¹ (frame G a) - frame F a = -y := by
    have : g (frame F a - y) = frame G a := by
      rw [map_sub]; simp only [LinearEquiv.coe_coe] at hye; rw [hye]; abel
    rw [← this]
    show g.symm (g (frame F a - y)) - frame F a = -y
    rw [LinearEquiv.symm_apply_apply]; abel
  rw [e]; exact neg_mem hy

theorem z_mem_orth {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : F.fl.z ∈ orth (VS D) (Xsp F) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  simp only [Xsp, FlagG.X] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact F.fl.z_orth i
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem nrat_adapt {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {n : GV D} (hn : n ∈ NRat F) : Adapt n F F := by
  refine ⟨hn.1, fun a => ?_⟩
  induction a using Fin.lastCases with
  | last =>
    rw [frame_last, Fin.val_last, xflag_top]
    exact hn.2.2 _ (z_mem_orth F)
  | cast i =>
    rw [frame_castSucc, Fin.coe_castSucc]
    exact hn.2.1 i.1 _ (Submodule.subset_span ⟨i, by simp, rfl⟩)

theorem gmap_mul (a b : GV D) (M : LV D) :
    Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_one (M : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) M = M := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_inj (g : GV D) {M N : LV D} (h : Formalism.HermitianLatticesTheory.gmap g M = Formalism.HermitianLatticesTheory.gmap g N) : M = N := by
  have := congrArg (Formalism.HermitianLatticesTheory.gmap g⁻¹) h
  rwa [← gmap_mul, ← gmap_mul, inv_mul_cancel, gmap_one, gmap_one] at this

theorem map_toO (g : GV D) (U : Submodule D.host.E (VS D).V) :
    (toO (VS D) U).map ((g : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) =
      toO (VS D) (U.map (g : (VS D).V →ₗ[D.host.E] (VS D).V)) := by
  ext x
  simp only [toO, Submodule.mem_map, Submodule.restrictScalars_mem, LinearMap.restrictScalars_apply]

theorem map_orth {g : GV D} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (U : Submodule D.host.E (VS D).V) :
    (orth (VS D) U).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) =
      orth (VS D) (U.map (g : (VS D).V →ₗ[D.host.E] (VS D).V)) := by
  ext y
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨w, hw, rfl⟩ x ⟨u, hu, rfl⟩
    rw [hg u w]; exact hw u hu
  · intro h
    refine ⟨g.symm y, fun x hx => ?_, by simp⟩
    have := h (g x) ⟨x, hx, rfl⟩
    rw [← hg x (g.symm y)]
    simpa using this

theorem lsub_map {T : D.host.E} {F G : LFlag (D.sp.Y 0) D.R.rS T} {g : GV D} (hg : Adapt g F G) (Λ : LV D) :
    Lsub (Formalism.HermitianLatticesTheory.gmap g Λ) G = Formalism.HermitianLatticesTheory.gmap g (Lsub Λ F) := by
  have hinj : Function.Injective ((g : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) :=
    g.injective
  simp only [Lsub, Lrep, Formalism.HermitianLatticesTheory.gmap]
  rw [Submodule.map_inf _ hinj, Submodule.map_sup, Submodule.map_inf _ hinj, map_toO, map_toO, map_orth hg.1,
    map_xsp hg]

theorem side : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (v : D.what₂.Word) (B : LFlag (D.sp.Y 0) D.R.rS ((Tu D v : ℕ) : D.host.E)) (ψ₀ ψ₁ : GV D) (Λa Λb : LV D), Λa ∈ Y.what₂ v → Λb ∈ Y.what₂ v → Adapt ψ₀ (lf D (X.Fu v)) B → Adapt ψ₁ (lf D (X.Fu v)) B → Lsub (Formalism.HermitianLatticesTheory.gmap ψ₀ Λa) B = Lsub (Formalism.HermitianLatticesTheory.gmap ψ₁ Λb) B → Λb = Λa ∧ ∃ n ∈ NRat (lf D (X.Fu v)), n * (ψ₁⁻¹ * ψ₀) ∈ Aut0 (lf D (X.Fu v)) Λa := by
  intro D X Y v B ψ₀ ψ₁ Λa Λb ha hb A0 A1 hL
  have As : Adapt (ψ₁⁻¹ * ψ₀) (lf D (X.Fu v)) (lf D (X.Fu v)) := adapt_mul A0 (adapt_inv A1)
  have hsub : Lsub (Formalism.HermitianLatticesTheory.gmap (ψ₁⁻¹ * ψ₀) Λa) (lf D (X.Fu v)) = Lsub Λb (lf D (X.Fu v)) := by
    apply gmap_inj ψ₁
    rw [← lsub_map A1, ← lsub_map A1, ← gmap_mul, mul_inv_cancel_left]
    exact hL
  obtain ⟨n, hn, hnΛ⟩ := _root_.GlobalTheory.Unfold.sameInner_unip D _ (X.Fu v) Λa Λb (ψ₁⁻¹ * ψ₀) ((Y.rowsOK v).1 Λa ha)
    ((Y.rowsOK v).1 Λb hb) As hsub
  have Ans : Adapt (n * (ψ₁⁻¹ * ψ₀)) (lf D (X.Fu v)) (lf D (X.Fu v)) := adapt_mul As (nrat_adapt hn)
  have heq : Λa = Λb := (GlobalTheory.T.row_representatives_up_to_frame_adapted_isometry D X Y v v).2 Λb hb Λa ha _ Ans hnΛ
  exact ⟨heq.symm, n, hn, Ans, hnΛ.trans heq.symm⟩

end GlobalTheory.Unfold.SideEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilUnitaryConvergentOfSiegelWeilConvergen
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain MeasureTheory Topology
open HeckeCharacterZeroLocus.SiegelWeilU

namespace GlobalTheory.SiegelWeilConvCompare

theorem exists_coord_pi {X : Type} [AddCommGroup X] [TopologicalSpace X] {k : ℕ}
    (e : X ≃ₜ (Fin k → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) (κ : Type) [Fintype κ] :
    ∃ (n : ℕ) (e' : (κ → X) ≃ₜ (Fin n → ℝ)), ∀ x y, e' (x + y) = e' x + e' y := by
  let e1 : (κ → X) ≃ₜ (κ → Fin k → ℝ) := Homeomorph.piCongrRight fun _ => e
  have h1 : ∀ x y, e1 (x + y) = e1 x + e1 y := by
    intro x y; funext i; exact he (x i) (y i)
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := κ → Fin k → ℝ)
    (F := Fin (Module.finrank ℝ (κ → Fin k → ℝ)) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e1.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e1 (x + y)) = L (e1 x) + L (e1 y)
  rw [h1, map_add (f := _)]

theorem exists_coord_Ainf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ (k : ℕ) (e : Ainf F ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  let e1 : Ainf F ≃ₜ (InfinitePlace F → ℝ) :=
    Homeomorph.piCongrRight fun v =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).toHomeomorph
  have h1 : ∀ x y, e1 (x + y) = e1 x + e1 y := by
    intro x y; funext v
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).map_add _ _
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := InfinitePlace F → ℝ)
    (F := Fin (Module.finrank ℝ (InfinitePlace F → ℝ)) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e1.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e1 (x + y)) = L (e1 x) + L (e1 y)
  rw [h1, map_add (f := _)]

theorem exists_coord_tens (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] :
    ∃ (k : ℕ) (e : Ainf F ⊗[F] E ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  classical
  let R := Ainf F
  let b := Module.Free.chooseBasis R (R ⊗[F] E)
  let eL : (R ⊗[F] E) ≃ₗ[R] (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) := b.equivFun
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  let e0 : R ⊗[F] E ≃ₜ (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) :=
    { toEquiv := eL.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap eL.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap }
  obtain ⟨k0, eA, hA⟩ := exists_coord_Ainf F
  obtain ⟨k, e1, h1⟩ := exists_coord_pi eA hA (Module.Free.ChooseBasisIndex R (R ⊗[F] E))
  refine ⟨k, e0.trans e1, fun x y => ?_⟩
  show e1 (e0 (x + y)) = e1 (e0 x) + e1 (e0 y)
  rw [show e0 (x + y) = e0 x + e0 y from eL.map_add x y, h1]

section Zero

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [Subsingleton V]

end Zero

theorem measure_fundamentalDomain_pos (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ) (hμ : IsHaarH F E σ M J μ)
    (𝓕) (h : IsFDH F E σ M J μ 𝓕) : 0 < μ 𝓕 := by
  haveI : μ.IsHaarMeasure := hμ
  haveI : Countable E := (Module.Free.chooseBasis ℚ E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
  haveI : Countable (GL (Fin M) E) := Units.val_injective.countable
  haveI : Countable (HFin (AF F) σ J) := by
    have : ((HFin (AF F) σ J : Subgroup (GL (Fin M) (AF F ⊗[F] E))) :
        Set (GL (Fin M) (AF F ⊗[F] E))).Countable := by
      unfold HFin; rw [Subgroup.coe_map]; exact (Set.to_countable _).image _
    exact this
  haveI : Countable (HFinIn (AF F) σ J) := by
    have : Function.Injective (fun x : HFinIn (AF F) σ J => (⟨x.1.1, x.2⟩ : HFin (AF F) σ J)) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : HFin (AF F) σ J => z.1) hxy))
    exact this.countable
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J))
  haveI : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  haveI : SMulInvariantMeasure (HFinIn (AF F) σ J) (HA (AF F) σ J) μ :=
    ⟨fun c s hs => measure_preimage_mul μ (show HA (AF F) σ J from c.1) s⟩
  exact pos_iff_ne_zero.2 (IsFundamentalDomain.measure_ne_zero (NeZero.ne μ) h)

section HermTop

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

def tensHomeo {κ : Type} [Finite κ] (b : Module.Basis κ F E) : R ⊗[F] E ≃ₜ (κ → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  { toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

end HermTop


end GlobalTheory.SiegelWeilConvCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAmplitudeFactorNonneg
section
noncomputable section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints

namespace GlobalTheory.TypeAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem termAmplitudeFactor_nonneg {D : D7} (large₂ : SizeData₂ D) (CH Cs C : ℝ) (hC : 0 ≤ C) (j : ℕ) (δ : ℕ → D.host.E) :
    0 ≤ k2a large₂ CH Cs C j δ := by
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have hS : 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := le_trans zero_le_one (one_le_sigma_product _ j δ)
  unfold k2a
  refine mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg hC (Nat.cast_nonneg _)) _)
    (Real.rpow_nonneg (minor_norm_nonneg j δ) _)) (Real.rpow_nonneg ?_ _)) (Real.rpow_nonneg hS _)
  unfold Formalism.MainNotions.S.Cnt.Hb
  exact Real.rpow_nonneg hb.le _

theorem typeBound_of_amplitude_pairs : AmpP → PairsP → TypeP := by
  intro hAmp hPairs Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CH, hCH, hA⟩ := hAmp Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨Ch, Cp, hCh, hCp, C'₁, Cl₁, hP⟩ := hPairs Cg cb Cw cT CT C0 CH hCH
  refine ⟨CH, Ch, Cp, hCH, hCh, hCp, fun Cs hCs => ?_⟩
  obtain ⟨C₀, hC₀, hA2⟩ := hA Cs (by linarith)
  refine ⟨C₀, fun C hC => ?_⟩
  obtain ⟨C'₂, Cl₂, hA3⟩ := hA2 C hC
  refine ⟨max C'₁ C'₂, max Cl₁ Cl₂, fun C' Cl hC' hCl D large₂ X Y u hTies hK hConc => ?_⟩
  have amp := hA3 C' Cl (le_of_max_le_right hC') (le_of_max_le_right hCl) D large₂ X Y u hTies hK hConc
  have pairs := hP C' Cl (le_of_max_le_left hC') (le_of_max_le_left hCl) D large₂ X Y u hK hConc
  intro j' hj' j'' hj'' δ' δ'' S hS
  have hC0 : 0 ≤ C := le_trans hC₀ hC
  have hdpi : 0 ≤ dpiC X u := Nat.cast_nonneg _
  have hsq : Real.sqrt (dpiC X u) * Real.sqrt (dpiC X u) = dpiC X u := Real.mul_self_sqrt hdpi
  have ha' := termAmplitudeFactor_nonneg large₂ CH Cs C hC0 j' δ'
  have ha'' := termAmplitudeFactor_nonneg large₂ CH Cs C hC0 j'' δ''
  have hK0 : 0 ≤ dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') :=
    mul_nonneg hdpi (mul_nonneg ha' ha'')
  have hterm : ∀ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≤
      dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := by
    intro p hp
    obtain ⟨hmem, hj1, hj2, hl1, hl2⟩ := hS p hp
    have h1 := amp p.1 hmem.1
    have h2 := amp p.2 hmem.2.1
    rw [hj1, hl1] at h1
    rw [hj2, hl2] at h2
    calc ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖
        ≤ (Formalism.L2.SG.TermOp.wt p.1 * Real.sqrt (dpiC X u) * (omT p.1 * k2a large₂ CH Cs C j' δ')) *
          (Formalism.L2.SG.TermOp.wt p.2 * Real.sqrt (dpiC X u) * (omT p.2 * k2a large₂ CH Cs C j'' δ'')) :=
          mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      _ = (Real.sqrt (dpiC X u) * Real.sqrt (dpiC X u)) * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
          ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := by ring
      _ = _ := by rw [hsq]
  calc ∑ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖
      ≤ ∑ p ∈ S, dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := Finset.sum_le_sum hterm
    _ = dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        ∑ p ∈ S, ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := by
      rw [Finset.mul_sum]
    _ ≤ dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        (massC Y u * (k2e large₂ CH Ch Cp j' δ' * k2e large₂ CH Ch Cp j'' δ'')) :=
      mul_le_mul_of_nonneg_left (pairs j' hj' j'' hj'' δ' δ'' S hS) hK0
    _ = _ := by ring

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOrbitsHeightsAmplitudesInCoordinates
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.WCoordTerms

theorem terms_orbits_heights_amps : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : WCoord P S), (∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → S.IsTerm (c.dat d) (c.lat t.abelian₂) ∧ LocNG.om P t = S.om (c.dat d) (c.lat t.abelian₂) ∧ (LocNG.BBne (H := H) t ↔ ¬ S.BBzero (c.dat d) (c.lat t.abelian₂))) ∧ (∀ d d' : LocNG.Datum P, LocNG.Datum.Rel d d' ↔ ∃ h ∈ S.H0, h • c.dat d = c.dat d') ∧ P.Hp = S.Hp ∧ (P.PrimeTo → S.Hp = 1) ∧ ∀ (R : LocNG.Reps P) (d : LocNG.Datum P), LocNG.amp R d (LocNG.BBne (H := H)) = S.amp (c.dat d) (fun Λ => ¬ S.BBzero (c.dat d) Λ) ∧ LocNG.amp R d (fun t => ¬ LocNG.BBne (H := H) t) = S.amp (c.dat d) (S.BBzero (c.dat d)) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  obtain ⟨P₂, c₂, φ, he, hSt, hK0, hUW, hHp, hPT, hdat, hterm, hom, hmov⟩ := _root_.GlobalTheory.HL.ToC.changed_duals M hM H r k P S c
  have hlat : ∀ Λ, c₂.lat Λ = c.lat Λ := fun Λ => by simp only [Coord.lat, WCoord.lat, he]
  have hrel : ∀ d d', LocNG.Datum.Rel d d' ↔ LocNG.Datum.Rel (φ d) (φ d') := by
    intro d d'
    unfold LocNG.Datum.Rel
    rw [hUW]
    exact exists_congr fun g => and_congr_right fun _ => hmov g d d'
  have hTR : LocNG.TRel P₂ = LocNG.TRel P := by
    funext t t'
    unfold LocNG.TRel
    rw [hSt]
  have hmu : ∀ t, LocNG.mu P₂ t = LocNG.mu P t := fun t => by
    unfold LocNG.mu
    rw [hSt, hK0]
  have T2 := GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P₂ S c₂
  have TD := GlobalTheory.HL.CoordDatum.transport M hM H r k P₂ S c₂
  have TH := GlobalTheory.HL.CoordHeight.height_eq M hM H r k P₂ S c₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d t ht
    have h := T2.1 (φ d) t ((hterm d t).1 ht)
    rw [hdat, hlat, hom d t ht] at h
    exact h
  · intro d d'
    rw [hrel, TD.2.2.1, hdat, hdat]
  · rw [← hHp]
    exact TH.1
  · intro hp
    obtain ⟨h1, h2, h3⟩ := TH.2.2 ((hPT).2 hp)
    have hvth : S.vth = 0 := by simp [Frames.vth, h1]
    have ha : S.a = 0 := by simp [Frames.a, h2, hvth]
    have hvD : S.vD = 0 := Finset.sum_eq_zero fun l _ => by
      split_ifs with h
      · exact h3 l h.2
      · rfl
    simp [Frames.Hp, hvth, ha, hvD]
  · intro R d
    let R₂ : LocNG.Reps P₂ :=
      { RD := φ '' R.RD
        RT := fun d₂ => R.RT (φ.symm d₂)
        hRD := by
          refine ⟨Set.subset_univ _, fun x _ => ?_, ?_⟩
          · obtain ⟨y, hy, hr⟩ := R.hRD.2.1 (φ.symm x) trivial
            refine ⟨φ y, ⟨y, hy, rfl⟩, ?_⟩
            have := (hrel y (φ.symm x)).1 hr
            rwa [φ.apply_symm_apply] at this
          · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
            exact congrArg φ (R.hRD.2.2 a ha b hb ((hrel a b).2 h))
        hRT := fun d₂ => by
          have hs : {t | LocNG.IsTermOver P₂ d₂ t} = {t | LocNG.IsTermOver P (φ.symm d₂) t} := by
            ext t
            simp only [Set.mem_setOf_eq]
            rw [hterm, φ.apply_symm_apply]
          rw [hs, hTR]
          exact R.hRT _ }
    have hamp : ∀ Q, LocNG.amp R d Q = LocNG.amp R₂ (φ d) Q := by
      intro Q
      unfold LocNG.amp
      have e : R₂.RT (φ d) = R.RT d := by simp [R₂]
      rw [e]
      refine tsum_congr fun t => ?_
      rw [hmu, hom d t.1 ((R.hRT d).1 t.2.1)]
    have A := GlobalTheory.HL.CoordAmp.amp_mass_eq M hM H r k P₂ S c₂ R₂ (φ d)
    rw [hdat] at A
    exact ⟨(hamp _).trans A.1, (hamp _).trans A.2.1⟩

end GlobalTheory.HL.WCoordTerms
end
end

