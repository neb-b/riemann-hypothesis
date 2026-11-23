module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.LiftLatInst
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Formalism.LocalToGlobal.Columns.Bundle0015
public import Formalism.LocalToGlobal.Columns.Bundle0007
public import Formalism.LocalToGlobal.Columns.WmpNatCardQuotEqPowFinrank
public import Formalism.LocalToGlobal.Columns.RowFormsGood
public import Formalism.LocalToGlobal.Columns.Bundle0009
public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2.Indef

section Conj

variable {K : Type} [Field K] {M M₂ : Type} [AddCommGroup M] [Module K M] [AddCommGroup M₂] [Module K M₂]
  (e : M ≃ₗ[K] M₂)

theorem conjE_one : e.conj (1 : Module.End K M) = 1 := by
  ext x
  simp [LinearEquiv.conj_apply]

theorem conjE_commute {f g : Module.End K M} (hfg : Commute f g) : Commute (e.conj f) (e.conj g) := by
  rw [commute_iff_eq]
  ext x
  simpa [LinearEquiv.conj_apply] using congrArg e (LinearMap.congr_fun hfg.eq (e.symm x))

theorem conjE_sub_pow (f : Module.End K M) (μ : K) (k : ℕ) :
    (e.conj f - μ • (1 : Module.End K M₂)) ^ k = e.conj ((f - μ • (1 : Module.End K M)) ^ k) := by
  have hsub : e.conj f - μ • (1 : Module.End K M₂) = e.conj (f - μ • (1 : Module.End K M)) := by
    ext x
    simp [LinearEquiv.conj_apply]
  rw [hsub]
  induction k with
  | zero => rw [pow_zero, pow_zero, conjE_one]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    ext x
    simp [LinearEquiv.conj_apply]

theorem conjE_maxGen (f : Module.End K M) (μ : K) :
    (e.conj f).maxGenEigenspace μ = (f.maxGenEigenspace μ).map (e : M →ₗ[K] M₂) := by
  ext y
  simp only [Module.End.mem_maxGenEigenspace, Submodule.mem_map, conjE_sub_pow]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨e.symm y, ⟨k, ?_⟩, by simp⟩
    simpa [LinearEquiv.conj_apply] using hk
  · rintro ⟨x, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by simp [LinearEquiv.conj_apply, hk]⟩

theorem conjE_iSup_maxGen (f : Module.End K M) (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) :
    ⨆ μ, (e.conj f).maxGenEigenspace μ = ⊤ := by
  simp only [conjE_maxGen]
  rw [← Submodule.map_iSup, hf, Submodule.map_top]
  exact LinearEquiv.range e

end Conj

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
  {ST SG' : Finset (HeightOneSpectrum (𝓞 E))}
  (S : Col.GSD K) (h : S.Ok) (c : Col.DecoPts S E n ST SG') (SG : Finset (HeightOneSpectrum (𝓞 E)))
  (S0 : Set (HeightOneSpectrum (𝓞 E)))

theorem heckeCSD_zero (P : offSub ST SG SG' S0) : heckeCSD S h c SG S0 (P, 0) = 1 := by
  unfold heckeCSD
  dsimp only
  first
    | (simp only [Col.heckeFam_zero]; ext x; simp [LinearEquiv.conj_apply])
    | (erw [Col.heckeFam_zero]; ext x; simp [LinearEquiv.conj_apply])
    | (ext x; simp [LinearEquiv.conj_apply, Col.heckeFam_zero])

theorem heckeCSD_comm (hc : Col.HeckeComm c S0) : Col.PairComm (heckeCSD S h c SG S0) := by
  intro x y
  exact conjE_commute _ (hc _ _)

theorem heckeCSD_split (hs : Col.HeckeFieldsIn c S0) : Col.SplitOver (heckeCSD S h c SG S0) := by
  intro x
  exact conjE_iSup_maxGen (S.res h) _ (hs _)

end Gen

section Tr

variable {X : Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : Col.CoefPk X n (Col.DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : Col.LevFam X.E X.K n SG)

theorem heckeFam_formPts_apply (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : Col.LevOff ST SG S0 × ℕ)
    (φ : (Col.formGSD C Λ).EqFun) :
    ((Col.heckeFam (formPts C Λ) S0 y φ : (Col.formGSD C Λ).EqFun) : Col.DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) =
      Col.nbFun X.K C.V y.1.1.asIdeal y.2 (φ : Col.DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) := by
  funext d
  simp only [Col.heckeFam, Col.heckeD]
  erw [Col.LocOp.ofNbr_op_apply]
  simp only [Col.DecoPts.nb, Finset.sum_map, LinearMap.id_apply]
  rfl

theorem heckeFam_comm_trRep {A : Type} [Group A] (ι : A →* Col.GLG (E := X.E) (n := n) (SG := SG)) (hι : ∀ a w, (Λ w).NormBy (ι a w))
    (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : Col.LevOff ST SG S0 × ℕ) (a : A) :
    Commute (Col.trRep C Λ ι hι a) (Col.heckeFam (formPts C Λ) S0 y) := by
  rw [commute_iff_eq]
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  have key : ∀ ψ : (Col.formGSD C Λ).EqFun,
      ((Col.trRep C Λ ι hι a ψ : (Col.formGSD C Λ).EqFun) : Col.DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) =
        Col.trF X n ST SG C.V (ι a) (ψ : Col.DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) := fun ψ => rfl
  rw [Module.End.mul_apply, Module.End.mul_apply, key, heckeFam_formPts_apply, heckeFam_formPts_apply, key,
    Col.trF_nbFun]

theorem heckeCSD_comm_trRep (h : (Col.formGSD C Λ).Ok) {A : Type} [Group A] (ι : A →* Col.GLG (E := X.E) (n := n) (SG := SG))
    (hι : ∀ a w, (Λ w).NormBy (ι a w)) (SG0 : Finset (HeightOneSpectrum (𝓞 X.E)))
    (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (x : offSub ST SG0 SG S0 × ℕ) (a : A) :
    Commute (heckeCSD (Col.formGSD C Λ) h (formPts C Λ) SG0 S0 x)
      ((Col.formGSD C Λ).repCSD h (Col.trRep C Λ ι hι) a) := by
  have hc := heckeFam_comm_trRep C Λ ι hι S0 (⟨x.1.1.1, x.1.2⟩, x.2) a
  have hr : (Col.formGSD C Λ).repCSD h (Col.trRep C Λ ι hι) a =
      ((Col.formGSD C Λ).res h).conj (Col.trRep C Λ ι hι a) := by
    apply LinearMap.ext
    intro f
    simp [Col.GSD.repCSD, LinearEquiv.conj_apply]
  rw [hr]
  exact conjE_commute ((Col.formGSD C Λ).res h) hc.symm

end Tr

section Inst

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}

abbrev rowPts (mu : Tup X.F X.E X.K S) :
    Col.DecoPts (Col.mtildeKGSD W Ch sel mu) X.E (R.N R.m - 1) ∅ (Col.rowSG Pr sel mu) := formPts _ _

abbrev liftPts (mu : Tup X.F X.E X.K S) (j : ℕ) :
    Col.DecoPts (Col.mtKGSD W Ch sel mu j) X.E R.nV ∅ (Col.rowSG Pr sel mu) := formPts _ _

structure ColHyp (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
    (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E))) : Prop where

  conj : IsConjAt v0

  irr : ∀ χ ∈ Xg, IsAbsIrrChar χ

  commR : ∀ τ : TupF TU, Col.HeckeComm (rowPts W Ch sel τ.1) S0

  splitR : ∀ τ : TupF TU, Col.HeckeFieldsIn (rowPts W Ch sel τ.1) S0

  commL : ∀ (j : Fin R.m) (τ : TupF TU), Col.HeckeComm (liftPts W Ch sel τ.1 (j.1 + 1)) S0

  splitL : ∀ (j : Fin R.m) (τ : TupF TU), Col.HeckeFieldsIn (liftPts W Ch sel τ.1 (j.1 + 1)) S0

variable (hX : X.Ok) (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)

theorem colFam_rows_ok (commR : ∀ τ : TupF TU, Col.HeckeComm (rowPts W Ch sel τ.1) S0)
    (splitR : ∀ τ : TupF TU, Col.HeckeFieldsIn (rowPts W Ch sel τ.1) S0) (τ : TupF TU) :
    ((colFam W Ch sel hX v0 TU Xg S0 xiVal).R τ).Ok 1 := by
  exact {
    good := Col.MtildeKCSD_good W Ch sel τ.1 hX _
    hrat := Col.CSDRat.H_mem _ (Col.MtildeKCSD_rat W Ch sel τ.1 hX _)
      (Col.csd_hasRatBasis _ (Col.MtildeKCSD_rat W Ch sel τ.1 hX _))
    hpos := fun v => (Col.mtildeK_rat W Ch sel τ.1 hX).posH _ v
    act := Col.unipotentActionForms_good W Ch sel τ.1 hX _
    actRat := Col.unipotentActionForms_rational W Ch sel τ.1 hX _
    comm := heckeCSD_comm _ _ _ _ _ (commR τ)
    split := heckeCSD_split _ _ _ _ _ (splitR τ)
    opG := fun i g => heckeCSD_comm_trRep _ _ _ _ _ _ _ i g
    blocks := Col.blockOk_firstValB (fun j (P : ↥(offSub ∅ Pr.vGs (Col.rowSG Pr sel τ.1) S0)) =>
        Ch.muVal j P.1.1 * xiVal τ.1 P.1.1) (q := fun P => Col.SplitOff.q P.1) R.r R.t_odd.pos
      (by have := R.two_le_m; omega) (fun P => Col.SplitOff.q_ne_zero P.1)
    q_pos := fun P => Nat.pos_of_ne_zero (Col.SplitOff.q_ne_zero P.1)
    pl_inj := Subtype.val_injective }

theorem colFam_lifts_ok (commL : ∀ (j : Fin R.m) (τ : TupF TU), Col.HeckeComm (liftPts W Ch sel τ.1 (j.1 + 1)) S0)
    (splitL : ∀ (j : Fin R.m) (τ : TupF TU), Col.HeckeFieldsIn (liftPts W Ch sel τ.1 (j.1 + 1)) S0)
    (j : Fin R.m) (τ : TupF TU) :
    ((colFam W Ch sel hX v0 TU Xg S0 xiVal).L j τ).Ok 1 := by
  exact {
    good := Col.MtKCSD_good W Ch sel τ.1 hX (j.1 + 1) _
    hrat := Col.CSDRat.H_mem _ (Col.MtKCSD_rat W Ch sel τ.1 hX (j.1 + 1) _)
      (Col.csd_hasRatBasis _ (Col.MtKCSD_rat W Ch sel τ.1 hX (j.1 + 1) _))
    hpos := fun v => (Col.mtK_rat W Ch sel τ.1 hX (j.1 + 1)).posH _ v
    act := Col.unipotentActionClassSum_good W Ch sel τ.1 hX (j.1 + 1) _
    actRat := Col.unipotentActionClassSum_rational W Ch sel τ.1 hX (j.1 + 1) _
    comm := heckeCSD_comm _ _ _ _ _ (commL j τ)
    split := heckeCSD_split _ _ _ _ _ (splitL j τ)
    opG := fun i g => heckeCSD_comm_trRep _ _ _ _ _ _ _ i g
    blocks := Col.blockOk_firstValA (fun (P : ↥(offSub ∅ Pr.vGs (Col.rowSG Pr sel τ.1) S0)) =>
        Ch.muVal j P.1.1 * xiVal τ.1 P.1.1) (fun P => Ch.etaVal P.1.1) (q := fun P => Col.SplitOff.q P.1) R.r
      R.t_odd.pos (fun P => Col.SplitOff.q_ne_zero P.1)
    q_pos := fun P => Nat.pos_of_ne_zero (Col.SplitOff.q_ne_zero P.1)
    pl_inj := Subtype.val_injective }

theorem colFam_ok (hH : ColHyp W Ch sel v0 TU Xg S0) : (colFam W Ch sel hX v0 TU Xg S0 xiVal).Ok 1 := by
  exact {
    conj := hH.conj
    tup_fin := tupF_finite TU
    irr := hH.irr
    what₂ := colFam_rows_ok W Ch sel hX v0 TU Xg S0 xiVal hH.commR hH.splitR
    lifts := colFam_lifts_ok W Ch sel hX v0 TU Xg S0 xiVal hH.commL hH.splitL }

end Inst

section Xi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

def IsUnifIdele (P : HeightOneSpectrum (𝓞 E)) (u : (AfE F E)ˣ) : Prop :=
  ∃ (v : HeightOneSpectrum (𝓞 F)) (hu : (u : AfE F E) ∈ RInt F E) (b : 𝓞 E),
    P.asIdeal.under (𝓞 F) = v.asIdeal ∧ u ∈ suppAt E v ∧ b ∈ P.asIdeal ∧ b ∉ P.asIdeal ^ 2 ∧
    (⟨(u : AfE F E), hu⟩ : RInt F E) - toRInt F E b ∈ (P.asIdeal ^ 2).map (toRInt F E) ∧
    ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (⟨(u : AfE F E), hu⟩ : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E)


open Classical in
def unifVal (ξ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) : Lˣ :=
  if h : ∃ u, IsUnifIdele (F := F) P u then ξ h.choose else 1

end Xi

section XiCol

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}

def xiVal (τ : Tup X.F X.E X.K S) (P : HeightOneSpectrum (𝓞 X.E)) : X.Kˣ := unifVal (τ : Chr X.F X.E X.K) P

variable (hX : X.Ok) (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))

end XiCol

section LinkCol

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok) (v0 : InfinitePlace X.K)
  (TU : Finset (Tup X.F X.E X.K S)) (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))


end LinkCol

end Formalism.L2.DIV
