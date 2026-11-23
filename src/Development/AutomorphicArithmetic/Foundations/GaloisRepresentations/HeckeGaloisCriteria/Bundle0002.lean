module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.LengthLeOfSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocus
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0368
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.InCongruenceModuleJeReCutTOfRestrict
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedMatchOfHeckeGalois
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0040

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.CompatibilityTiesEigenRestriction
section
noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Alg

def descHom {O X M B : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] [Semiring B] [Algebra O B]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M) (S : Set X) (z : B →ₐ[O] Module.End O M)
    (h : ∀ b (f : T), z b * act f = act f * z b) : B →ₐ[O] Module.End O (cutM T act S) where
  toFun b := desc T act S (z b) (h b)
  map_one' := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [desc_mk, map_one]; rfl
  map_mul' a b := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [Module.End.mul_apply, desc_mk, desc_mk, desc_mk, map_mul]; rfl
  map_zero' := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [desc_mk, map_zero]; rfl
  map_add' a b := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [LinearMap.add_apply, desc_mk, desc_mk, desc_mk, map_add (f := _), LinearMap.add_apply, map_add (f := _)]
  commutes' a := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [desc_mk, AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]

variable {D : D7} (c : CutD D)

def zCut (Q : PairedCharacterCondition.Pend D) (i : D.nd.Loc) (S : Set (D.nd.X i)) :
    ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) →ₐ[D.nd.O i]
      Module.End (D.nd.O i) (cutM (D.nd.T i) (D.nd.act i) S) :=
  descHom (D.nd.T i) (D.nd.act i) S (Q.zO i) (Q.zO_comm i)


set_option maxHeartbeats 2000000 in
def pendCut (Q : PairedCharacterCondition.Pend D) : PairedCharacterCondition.Pend (cut D c) where
  lz := Q.lz
  eSer_eq := Q.eSer_eq
  eSer_LL := Q.eSer_LL
  zetaPrimitiveRoot := fun i => Q.zetaPrimitiveRoot i.1
  om := Q.om
  om_one := Q.om_one
  om_mul := Q.om_mul
  tameInertiaChar_mul_root := Q.tameInertiaChar_mul_root
  om_wild := Q.om_wild
  om_open := Q.om_open
  om_inj := Q.om_inj
  om_tg := Q.om_tg
  inertiaCharpoly_eigenvalues := Q.inertiaCharpoly_eigenvalues
  inertiaCharpoly_character := Q.inertiaCharpoly_character
  zO := fun i => zCut Q i.1 (c.Xs i.1)
  zO_comm := fun i z f => desc_comm (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) _ (Q.zO_comm i.1 z) f
  zL_stable := fun i => Q.zL_stable i.1
  zO_act := fun i z x y h =>
    (congrArg (qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1)) (Q.zO_act i.1 z x y h)).trans
      (qK_desc (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) _ (Q.zO_comm i.1 z) _).symm
  prMt_type := fun i PI x hx => by
    obtain ⟨a, b⟩ := Q.prMt_type i.1 PI x hx
    refine ⟨fun p hp => qK_mem (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (x := p) (a p.1 (optIn_eq_some.1 hp)), fun hn => ?_⟩
    show qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (D.nd.prMt i.1 x) = 0
    cases hp : D.naut.ptV i.1 PI with
    | none => rw [b hp, map_zero]
    | some p =>
      refine qK_out (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (D.nd.T_sep i.1) (x := p) (fun hm => ?_) (a p hp)
      have := (optIn_eq_some (S := c.Xs i.1) (x := ⟨p, hm⟩)).2 hp
      exact Option.some_ne_none _ (this.symm.trans hn)
  Par_surj := fun i x Sig h => Q.Par_surj i.1 x.1 Sig (h.imp fun _ k => ⟨optIn_eq_some.1 k.1, k.2⟩)
  kty := fun i => Q.kty i.1
  kty_spec := fun i => Q.kty_spec i.1

theorem eigSpan_cut {Q : PairedCharacterCondition.Pend D} (h : GlobalTheory.Pass.EigSpan Q) : GlobalTheory.Pass.EigSpan (pendCut c Q) := by
  intro i z x a ha u hu
  have hu' : u ∈ (heckeEig (D.nd.T i.1) (D.nd.act i.1) x.1).map (qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1)) := by
    rw [map_eig _ _ _ (D.nd.T_sep i.1) x]; exact hu
  obtain ⟨v, hv, rfl⟩ := hu'
  have e := h i.1 z x.1 a (fun PI hP => ha PI (optIn_eq_some.2 hP)) v hv
  refine (qK_desc (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) _ (Q.zO_comm i.1 z) v).trans ?_
  rw [e]
  have k : ∀ (b : D.nd.O i.1) (w : TensorProduct (D.nd.O i.1) (FractionRing (D.nd.O i.1)) (D.nd.Mt i.1)),
      qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (b • w) = b • qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) w := fun b w => by
    rw [← algebraMap_smul (FractionRing (D.nd.O i.1)) b w, map_smul, algebraMap_smul]
  exact k a v

theorem compatibilityTies_eigenRestriction (h : Tie4 D) : Tie4 (cut D c) := by
  obtain ⟨a, ⟨Q, hDZ, hE⟩, b, d⟩ := h
  exact ⟨fun i => a i.1, ⟨pendCut c Q, fun i => hDZ i.1, eigSpan_cut c hE⟩, fun i => b i.1, fun i => d i.1⟩

end UpperTheory.GalC
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.IsHeckeGaloisIff
section
noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.HeightCounting Alg TensorProduct

variable {D : D7} {c : CutD D}

theorem mem_Zgood {i : (cut D c).nd.Loc} {x : (cut D c).nd.X i} : x ∈ (cut D c).nd.Zgood i ↔ x.1 ∈ D.nd.Zgood i.1 := by
  classical
  exact Finset.mem_subtype

theorem eta_le (h : c.Good) (i : (cut D c).nd.Loc) : D.nd.etaLoc i.1 ≤ (cut D c).nd.etaLoc i +
    (∑ x ∈ D.nd.Zgood i.1, D.nd.mult i.1 x : ℕ) * (padicValNat (D.nd.l i.1) D.what₂.restRowsFiniteGroupCard : ℚ) := by
  classical
  obtain ⟨α, -, hα1, hα2⟩ := h.op i.1 i.2
  have hn : D.what₂.restRowsFiniteGroupCard ≠ 0 := (D.what₂.restRowsFiniteGroupCard_pos).ne'
  have hA : ((D.what₂.restRowsFiniteGroupCard : ℕ) : D.nd.O i.1) ≠ 0 := by
    intro hz
    have h1 : ((D.what₂.restRowsFiniteGroupCard : D.what₂.LL) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have h2 : D.nd.embK i.1 (D.what₂.restRowsFiniteGroupCard : D.what₂.LL) = 0 := by
      rw [map_natCast, ← map_natCast (algebraMap (D.nd.O i.1) (FractionRing (D.nd.O i.1))), hz, map_zero]
    exact h1 ((map_eq_zero_iff _ (D.nd.embK i.1).injective).mp h2)
  have hα1' : ∀ x ∈ D.nd.Zgood i.1, ∀ u ∈ heckeEig (D.nd.T i.1) (D.nd.act i.1) x,
      (LinearMap.baseChange (FractionRing (D.nd.O i.1)) α) u = ((D.what₂.restRowsFiniteGroupCard : ℕ) : D.nd.O i.1) • u := by
    intro x hx u hu
    rw [hα1 x hx u hu, Int.cast_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hY : ∀ x : ↥(c.Xs i.1), x ∈ (((cut D c).nd.Zgood i : Finset ((cut D c).nd.X i)) : Set ((cut D c).nd.X i)) ↔
      (x : D.nd.X i.1) ∈ D.nd.Zgood i.1 :=
    fun x => Iff.trans Finset.mem_coe mem_Zgood
  have key := Alg.length_le (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (D.nd.T_sep i.1) (D.nd.Zgood i.1) _ hY α _ hA hα1' hα2
  have hfinE : Module.length (D.nd.O i.1) (D.nd.O i.1 ⧸ Ideal.span {((D.what₂.restRowsFiniteGroupCard : ℕ) : D.nd.O i.1)}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero hA))
  have hpad := GlobalTheory.CutAtGood.lenUnit_natCast_le i.1 D.what₂.restRowsFiniteGroupCard hn
  refine (Alg.lenUnit_le_add (D.nd.l i.1) _ hfinE (fun hC => absurd hC ?_) key).trans ?_
  · exact Alg.length_ne_top ((cut D c).nd.T i) ((cut D c).nd.act i) ((cut D c).nd.T_sep i) ((cut D c).nd.Zgood i)
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpad (Nat.cast_nonneg _))

theorem eta_zero {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (h : N.Zgood i = ∅) :
    N.etaLoc i = 0 := by
  have hsum : N.eigSum i ↑(N.Zgood i) = ⊥ := by
    rw [h]
    simp [NData.eigSum]
  have hup : N.MtUp i = ⊥ := by
    simp [NData.MtUp, hsum]
  have hsub : Subsingleton (N.MtUp i) := by
    rw [hup]
    infer_instance
  have hq : Subsingleton (↥(N.MtUp i) ⧸ Submodule.comap (N.MtUp i).subtype (N.MtLow i)) := by
    infer_instance
  unfold NData.etaLoc lenUnit
  rw [Module.length_eq_zero]
  simp

theorem etaJ_le (h : c.Good) (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    (D.what₂.etaJ j w : ℝ) ≤ ((cut D c).what₂.etaJ j w : ℝ) +
      (∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) *
        (padicValNat (D.what₂.places.resChar w) D.what₂.restRowsFiniteGroupCard : ℝ) := by
  classical
  let F : D.nd.Loc → ℚ := fun i => if hk : c.keep i then (cut D c).nd.etaLoc (⟨i, hk⟩ : (cut D c).nd.Loc) else 0
  have hcut : (cut D c).what₂.etaJ j w = ∑ i ∈ D.nd.locs j w, F i := by
    rw [(cut D c).etaJ_tie j w h1 h2]
    show ∑ i ∈ Finset.subtype c.keep (D.nd.locs j w), (cut D c).nd.etaLoc i = _
    have hF : ∀ i ∈ Finset.subtype c.keep (D.nd.locs j w), (cut D c).nd.etaLoc i = F i.1 := by
      intro i _
      simp only [F, dif_pos i.2]
    rw [Finset.sum_congr rfl hF, Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_filter_of_ne ?_
    intro i _ hne
    by_contra hk
    exact hne (dif_neg hk)
  have hD := D.etaJ_tie j w h1 h2
  have hpt : ∀ i ∈ D.nd.locs j w, D.nd.etaLoc i ≤ F i +
      (∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℚ)) * (padicValNat (D.what₂.places.resChar w) D.what₂.restRowsFiniteGroupCard : ℚ) := by
    intro i hi
    have hw : D.nd.w i = w := ((D.nd.locs_mem j w i).mp hi).2
    have hl : D.what₂.places.resChar w = D.nd.l i := by
      rw [← hw]
      exact D.nd.w_l i
    rw [hl]
    by_cases hk : c.keep i
    · have hb := eta_le h (⟨i, hk⟩ : (cut D c).nd.Loc)
      simp only [F, dif_pos hk]
      push_cast at hb
      exact hb
    · have hz : D.nd.Zgood i = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        exact fun hne => hk ((h.keep i).mpr hne)
      rw [eta_zero D.nd i hz]
      simp only [F, dif_neg hk, zero_add]
      positivity
  have hQ : D.what₂.etaJ j w ≤ (cut D c).what₂.etaJ j w +
      (∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℚ)) *
        (padicValNat (D.what₂.places.resChar w) D.what₂.restRowsFiniteGroupCard : ℚ) := by
    rw [hD, hcut, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hpt
  exact_mod_cast hQ

end UpperTheory.GalC
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.KapSharpTr
section
noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7} (Λ : CutD D)

set_option maxHeartbeats 1600000

@[reducible] def sideTr {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) :
    RowSide (cut D Λ) EE := { S with }

section Side

variable {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)

theorem downTo_tr (μ : D.what₂.Tup) (j : ℕ) : (sideTr Λ S).downTo μ j = S.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg (fun f => f.comp (S.io μ j)) ih

theorem iota_tr (μ : D.what₂.Tup) : (sideTr Λ S).iota μ = S.iota μ := by
  unfold RowSide.iota; rw [downTo_tr]; rfl

theorem Qsp_tr (μ : D.what₂.Tup) : (sideTr Λ S).Qsp μ = S.Qsp μ := by
  unfold RowSide.Qsp RowSide.Usp; rw [iota_tr]; rfl

theorem RRset_tr (μ : D.what₂.Tup) : (sideTr Λ S).RRset μ = S.RRset μ := by
  unfold RowSide.RRset RowSide.LamSet; rw [iota_tr]; simp only [Qsp_tr]; rfl

theorem iiStar_tr : (sideTr Λ S).iiStar = S.iiStar := by
  have key : ∀ (f f' : S.Amb D.what₂.mu0 →ₗ[ℂ] EE) (Q Q' : Submodule ℂ (S.Amb D.what₂.mu0)), f = f' → Q = Q' →
      f.domRestrict Q ∘ₗ LinearMap.adjoint (f.domRestrict Q) = f'.domRestrict Q' ∘ₗ LinearMap.adjoint (f'.domRestrict Q') := by
    rintro _ _ _ _ rfl rfl; rfl
  exact key _ _ _ _ (iota_tr Λ S _) (Qsp_tr Λ S _)

theorem kapOf_tr {n : ℕ} (ty : Fin n → D.what₂.FT) : (sideTr Λ S).kapOf ty = S.kapOf ty := by
  unfold RowSide.kapOf RowSide.kapRatio; rw [iiStar_tr]; rfl

theorem rrDef_tr (H : S.RRDef) : (sideTr Λ S).RRDef := by
  have e : (sideTr Λ S).RRset = S.RRset := funext (RRset_tr Λ S)
  unfold RowSide.RRDef; rw [e]; exact H

end Side

theorem kapSharp_tr : kapSharp (cut D Λ) = kapSharp D := kapOf_tr Λ (RowSide.sharp D) _

def ambTr {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {S : RowSide D EE} (x : AmbForm D S) :
    AmbForm (cut D Λ) (sideTr Λ S) := { x with }

end UpperTheory.GalC
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.NchTieTr
section
noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7} (Λ : CutD D)

set_option maxHeartbeats 1600000

@[reducible] def nchTr (x : NChoice D) : NChoice (cut D Λ) := { x with }

@[reducible] def xdTr (x : ThData D) : ThData (cut D Λ) := { x with }

theorem nchTie_tr {x : NChoice D} (H : NChTie D x) : NChTie (cut D Λ) (nchTr Λ x) :=
  { H with
    twOf_eq := fun a => H.twOf_eq a.1
    twSide_eq := fun a => H.twSide_eq a.1
    Q_eq := fun a => H.Q_eq a.1
    psi_eq := H.psi_eq.imp fun _ k => ⟨k.1, k.2.1, fun a => k.2.2 a.1⟩ }

theorem sLen_tr (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ) (Q : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))) (ψ : BlochKatoReduction.Gen.GE D.nd →* (D.ntw.Ok i k)ˣ) :
    BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 (cut D Λ)) i s k Q ψ = BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) i s k Q ψ := by
  delta BlochKatoReduction.Gen.sLen BlochKatoReduction.Gen.selT BlochKatoReduction.Gen.bk BlochKatoReduction.Gen.Trep BlochKatoReduction.Gen.Tgl BlochKatoReduction.Gen.IsImgK BlochKatoReduction.Gen.IsFrac BlochKatoReduction.Gen.phiK BlochKatoReduction.Gen.chiS BlochKatoReduction.Gen.Spl BlochKatoReduction.bk0 BlochKatoReduction.Gen.PDv BlochKatoReduction.Gen.repV BlochKatoReduction.Gen.DecV BlochKatoReduction.Gen.GE
  dsimp +instances only [cut, GlobalTheory.HeightCounting.setRaw, GlobalTheory.HeightCounting.NLay0.reEta, layCut, ndCut, GlobalTheory.HeightCounting.rowsEta]
  congr 1

theorem twAt_tr {x : NChoice D} {y : ThData D} (H : LocalQuadraticParts.TWAt D x y) : LocalQuadraticParts.TWAt (cut D Λ) (nchTr Λ x) (xdTr Λ y) := by
  obtain ⟨hc, N0, S, H⟩ := H
  refine ⟨hc, N0, S, fun w hw => ⟨(H w hw).1, ?_⟩⟩
  obtain ⟨h1, h2, h3, ⟨e, h4, h4', h4''⟩, h5, h6⟩ := (H w hw).2
  exact ⟨h1, h2, h3, ⟨e, h4, h4', fun s hs => (sLen_tr Λ _ s _ _ _).trans_le (h4'' s hs)⟩, h5, h6⟩

end UpperTheory.GalC
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.Tie0CutOfTie0
section
noncomputable section

namespace UpperTheory.GalC.Tr

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.NRows

variable {D : D7} {c : CutD D}

theorem ptV_iff (i : (cut D c).nd.Loc) (P : D.naut.AV i.1) (x : (cut D c).nd.X i) :
    (cut D c).naut.ptV i P = some x ↔ D.naut.ptV i.1 P = some x.1 := optIn_eq_some

theorem par_iff (i : (cut D c).nd.Loc) (x : (cut D c).nd.X i) (Sig : List (Part D.naut.CG)) :
    HasParamX (cut D c).nd (cut D c).naut i x Sig ↔ HasParamX D.nd D.naut i.1 x.1 Sig :=
  exists_congr fun _ => and_congr optIn_eq_some Iff.rfl

theorem zn_iff (i : (cut D c).nd.Loc) (x : (cut D c).nd.X i) :
    x ∈ ZN (cut D c).nd (cut D c).naut i ↔ x.1 ∈ ZN D.nd D.naut i.1 :=
  exists_congr fun _ => and_congr optIn_eq_some Iff.rfl

theorem zg_iff (i : (cut D c).nd.Loc) (x : (cut D c).nd.X i) :
    x ∈ ZgoodN (cut D c).nd (cut D c).naut i ↔ x.1 ∈ ZgoodN D.nd D.naut i.1 :=
  and_congr (zn_iff i x) (exists_congr fun Sig => and_congr (par_iff i x Sig) Iff.rfl)

theorem z_iff (i : (cut D c).nd.Loc) (x : (cut D c).nd.X i) : x ∈ (cut D c).nd.Z i ↔ x.1 ∈ D.nd.Z i.1 :=
  ((cut D c).Z_tie i x).trans ((zn_iff i x).trans (D.Z_tie i.1 x.1).symm)

theorem hg_of {i : (cut D c).nd.Loc} (h : HG (cut D c).nd (cut D c).naut i) : HG D.nd D.naut i.1 :=
  h.elim fun x hx => ⟨x.1, (zg_iff i x).1 hx⟩

theorem eigC_eq (i : (cut D c).nd.Loc) (x : (cut D c).nd.X i) :
    eigC (cut D c).nd (cut D c).naut i x = eigC D.nd D.naut i.1 x.1 := by
  have e : {P | (cut D c).naut.ptV i P = some x} = {P | D.naut.ptV i.1 P = some x.1} := Set.ext fun P => ptV_iff i P x
  unfold eigC
  rw [e]; rfl

theorem res_eq {O X : Type} [CommRing O] [IsLocalRing O] (T : Subalgebra O (X → O)) [IsLocalRing T] (f : T) (x y : X) :
    IsLocalRing.residue O ((f : X → O) x) = IsLocalRing.residue O ((f : X → O) y) := by
  let g : T := f - algebraMap O T ((f : X → O) x)
  have hx : (g : X → O) x = 0 := by simp [g]
  have hg : ¬ IsUnit g := fun h => by
    have := h.map ((Pi.evalRingHom (fun _ : X => O) x).comp T.val.toRingHom)
    have e : ((Pi.evalRingHom (fun _ : X => O) x).comp T.val.toRingHom) g = 0 := hx
    rw [e] at this
    exact not_isUnit_zero this
  have hy : ¬ IsUnit ((g : X → O) y) := fun h => by
    obtain ⟨u, hu⟩ := h
    let k : T := 1 - algebraMap O T (↑u⁻¹ : O) * g
    have hk : IsUnit k := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (algebraMap O T (↑u⁻¹ : O) * g) with h | h
      · exact absurd (isUnit_of_mul_isUnit_right h) hg
      · exact h
    have := hk.map ((Pi.evalRingHom (fun _ : X => O) y).comp T.val.toRingHom)
    have e : ((Pi.evalRingHom (fun _ : X => O) y).comp T.val.toRingHom) k = 0 := by
      show (1 : O) - (↑u⁻¹ : O) * (g : X → O) y = 0
      rw [← hu, Units.inv_mul, sub_self]
    rw [e] at this
    exact not_isUnit_zero this
  have e : (g : X → O) y = (f : X → O) y - (f : X → O) x := by simp [g]
  rw [e] at hy
  rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hy

theorem hecke_res (D : D7) (i : D.nd.Loc) (x y : D.nd.X i) (w : PlE D.host) :
    (heckePol D.nd i x w).map (IsLocalRing.residue (D.nd.O i)) = (heckePol D.nd i y w).map (IsLocalRing.residue (D.nd.O i)) := by
  haveI := D.nd.T_local i
  unfold heckePol
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.map_add (f := _), Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, map_mul, res_eq (D.nd.T i) _ x y]

theorem atM_iff (i : (cut D c).nd.Loc) (σ : D.what₂.FT) : AtM (cut D c).nd (cut D c).naut i σ ↔ AtM D.nd D.naut i.1 σ := by
  refine exists_congr fun Sig => and_congr Iff.rfl ⟨fun ⟨x, h⟩ => ⟨x.1, h⟩, fun ⟨x, h⟩ => ?_⟩
  obtain ⟨y⟩ := (cut D c).nd.neX i
  refine ⟨y, fun w hw => ?_⟩
  obtain ⟨p, h1, h2⟩ := h w hw
  exact ⟨p, h1, h2.trans (hecke_res D i.1 x y.1 w)⟩

theorem rhoBar_iff (i : (cut D c).nd.Loc) (rb : G D.host.E D.nd.Om →* GL (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O i.1))) :
    IsRhoBar (cut D c).nd i rb ↔ IsRhoBar D.nd i.1 rb := by
  refine and_congr Iff.rfl ⟨fun h x w hw B σ hB hσ => ?_, fun h x => h x.1⟩
  obtain ⟨y⟩ := (cut D c).nd.neX i
  exact (h y w hw B σ hB hσ).trans (hecke_res D i.1 y.1 x w)

theorem goodPart_eq (i : (cut D c).nd.Loc) : goodPartM (cut D c).nd (cut D c).naut i = goodPartM D.nd D.naut i.1 := by
  have e : {σ | (cut D c).nd.goodRow σ ∧ AtM (cut D c).nd (cut D c).naut i σ} = {σ | D.nd.goodRow σ ∧ AtM D.nd D.naut i.1 σ} :=
    Set.ext fun σ => and_congr Iff.rfl (atM_iff i σ)
  unfold goodPartM
  rw [e]; rfl

theorem iSup_good (hc : c.Good) (i : (cut D c).nd.Loc) {α : Type} [CompleteLattice α] (F : D.nd.X i.1 → α) :
    ⨆ x ∈ ZgoodN (cut D c).nd (cut D c).naut i, F x.1 = ⨆ x ∈ ZgoodN D.nd D.naut i.1, F x :=
  le_antisymm (iSup₂_le fun x hx => le_iSup₂_of_le (f := fun x _ => F x) x.1 ((zg_iff i x).1 hx) le_rfl)
    (iSup₂_le fun x hx => le_iSup₂_of_le (f := fun (x : (cut D c).nd.X i) _ => F x.1)
      ⟨x, hc.good i.1 x ((D.Zgood_tie i.1 x).2 hx)⟩ ((zg_iff i _).2 hx) le_rfl)

theorem tie0_cut_of_tie0 (h : SumRepresentations.tie0 D) : SumRepresentations.tie0 (cut D c) :=
  ⟨h.1, ⟨h.2.1.1, h.2.1.2.1, h.2.1.2.2.1, fun i => h.2.1.2.2.2 i.1⟩,
    fun i => h.2.2.1 i.1, fun i => h.2.2.2.1 i.1, fun i => h.2.2.2.2.1 i.1, fun i => h.2.2.2.2.2 i.1⟩

theorem fourthAdmissible_restrictToPoints (h : SumRepresentations.ArchimedeanSignatureMatching D) : SumRepresentations.ArchimedeanSignatureMatching (cut D c) := ⟨fun i => h.1 i.1, fun i => h.2.1 i.1, h.2.2⟩
theorem hypO_cut (h : SumRepresentations.hypO D) : SumRepresentations.hypO (cut D c) := fun i x => h i.1 x.1
theorem rhoBar_cut (h : ResidualIrreducibleRankR D) : ResidualIrreducibleRankR (cut D c) := fun i hg rb hrb => h i.1 (hg_of hg) rb ((rhoBar_iff i rb).1 hrb)

theorem rowsB_cut (h : RowsB D) : RowsB (cut D c) :=
  { rowSize := fun i => h.rowSize i.1, a3 := fun i => h.a3 i.1, a4 := fourthAdmissible_restrictToPoints h.a4, thetaOne := fun i => h.thetaOne i.1 }

theorem rowsC_cut (hc : c.Good) (h : RowsC D) : RowsC (cut D c) :=
  { c4b := fun σ k v h1 h2 i => h.c4b σ k v h1 h2 i.1
    rho := fun i x hx Sig hS => h.rho i.1 x.1 ((zg_iff i x).1 hx) Sig ((par_iff i x Sig).1 hS)
    dz := fun i x hx Sig hS => h.dz i.1 x.1 ((zg_iff i x).1 hx) Sig ((par_iff i x Sig).1 hS)
    parUp := fun i x hx Sig hS => by
      rw [eigC_eq]; exact h.parUp i.1 x.1 ((zg_iff i x).1 hx) Sig ((par_iff i x Sig).1 hS)
    downMem := fun i x hx Sig hS => by
      rw [eigC_eq]; exact h.downMem i.1 x.1 ((zg_iff i x).1 hx) Sig ((par_iff i x Sig).1 hS)
    goodPart := fun i => by
      refine (goodPart_eq i).trans ((h.goodPart i.1).trans ((iSup_good hc i _).symm.trans ?_))
      refine iSup_congr fun x => iSup_congr fun _ => ?_
      have e : {Sig | HasParamX (cut D c).nd (cut D c).naut i x Sig} = {Sig | HasParamX D.nd D.naut i.1 x.1 Sig} :=
        Set.ext fun Sig => par_iff i x Sig
      rw [e]; rfl }


set_option maxHeartbeats 1000000 in
def ledBack (L : SizeData₂ (cut D c)) : SizeData₂ D := { L with }

theorem pointsAdmissible_restrictToPoints (hc : c.Good) (h : SumRepresentations.ConclusionZ D) : SumRepresentations.ConclusionZ (cut D c) := by
  classical
  intro i hg
  obtain ⟨a, b, d⟩ := h i.1 (hg_of hg)
  refine ⟨fun x hx Sig hS => ?_, ?_, ?_⟩
  · rw [eigC_eq]; exact a x.1 ((zg_iff i x).1 hx) Sig ((par_iff i x Sig).1 hS)
  · rw [goodPart_eq]
    refine b.trans ((iSup_good hc i _).symm.trans (iSup_congr fun x => iSup_congr fun _ => (eigC_eq i x).symm))
  · have e : dM (cut D c).nd (cut D c).naut i = dM D.nd D.naut i.1 := by unfold dM; rw [goodPart_eq]; rfl
    rw [e, ← d]
    refine Finset.sum_of_injOn (fun x => x.1) (fun x _ y _ k => Subtype.ext k) (fun _ _ => Finset.mem_univ _)
      (fun x _ hx => if_neg fun hz => hx ⟨⟨x, hc.good i.1 x ((D.Zgood_tie i.1 x).2 hz)⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩)
      fun x _ => ?_
    have m : (cut D c).nd.mult i x = D.nd.mult i.1 x.1 := Alg.mult_eq _ _ _ (D.nd.T_sep i.1) x
    by_cases hz : x.1 ∈ ZgoodN D.nd D.naut i.1
    · rw [if_pos hz, if_pos ((zg_iff i x).2 hz), m]
    · rw [if_neg hz, if_neg fun k => hz ((zg_iff i x).1 k)]

theorem jointCondition_restrictToPoints (h : KillingConditions.LocalisationUniqueness D) : KillingConditions.LocalisationUniqueness (cut D c) :=
  fun i i' h1 h2 h3 σ hσ a b => Subtype.ext (h i.1 i'.1 h1 h2 h3 σ hσ ((atM_iff i σ).1 a) ((atM_iff i' σ).1 b))

theorem live_of {i : (cut D c).nd.Loc} (h : GlobalTheory.CoefDuty.Live (cut D c).nd i) : GlobalTheory.CoefDuty.Live D.nd i.1 := by
  obtain ⟨π, hπ, k⟩ := h
  exact ⟨π.1, (z_iff i π).1 hπ, k⟩

theorem large_cut (h : GlobalTheory.CoefDuty.Large D) : GlobalTheory.CoefDuty.Large (cut D c) := by
  refine ⟨hypO_cut h.1, fun i x => h.2.1 i.1 x.1, fun i hl => ?_⟩
  obtain ⟨r, ρ, hr, A, i1, i2, i3, i4, i5, i6, i7, TA, repA, ρA, χA, hE, hS, hC⟩ := h.2.2 i.1 (live_of hl)
  haveI : Nonempty (c.Xs i.1) := (c.ne i.1 i.2).to_subtype
  refine ⟨fun x => r x.1, fun x => ρ x.1, fun x => hr x.1, A, i1, i2, i3, i4, i5, i6, i7, Alg.cutT TA (c.Xs i.1),
    fun x => repA x.1, fun x => ρA x.1, χA,
    ⟨hE.1, span_cut (O := D.nd.O i.1) (TO := D.nd.T i.1) (c.Xs i.1) hE.2.1, fun x => hE.2.2.1 x.1, fun x hx => hE.2.2.2.1 x.1 ((z_iff i x).1 hx), hE.2.2.2.2⟩,
    setting_cut _ (fun y hy => (z_iff i y).1 hy) hS, fun π hπ => ?_⟩
  obtain ⟨g0, L, eB, e1, X0, a, b, d⟩ := hC π.1 ((z_iff i π).1 hπ)
  exact ⟨g0, L, fun y => eB y.1, fun y => e1 y.1, fun y => X0 y.1, a, isChoice_cut _ b, fun x => d x.1⟩

theorem cutRec_cut (hc : c.Good) : CutRec (cut D c) := by
  intro i P hP k w hw
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hP
  exact hc.nice i.1 i.2 P x.1 x.2 ((ptV_iff i P x).1 hx) k w hw

end UpperTheory.GalC.Tr
end
end

