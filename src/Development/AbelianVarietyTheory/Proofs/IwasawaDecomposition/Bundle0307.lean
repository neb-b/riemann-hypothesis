module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0294
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvSmulMemOfRedL
public import Formalism.LocalToGlobal.Columns.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RbarData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

def ssRep {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) : Γ →* GL (Fin a) k :=
  Classical.epsilon fun ρ' : Γ →* GL (Fin a) k => IsSSRep ρ' ∧ ρ.ker ≤ ρ'.ker ∧
    ∀ g, (ρ' g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly

def BcGood (D : D7) (Rw : RowSide D) (σ : D.what₂.FT) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) : Prop :=
  (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π ∧ ∀ τ, (D.naut.infG p.π τ).Nodup ∧
      ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.r : ℂ) - (p.d : ℂ)) / 2) ∧
  rankIso D.nd D.naut Sig = D.R.r ∧ ∀ w, IsSplitPl D.host w → isoLoc D.nd D.naut Sig w = Rw.locR σ w


open Classical in
def bcOf (D : D7) (Rw : RowSide D) (σ : D.what₂.FT) : Multiset (ℕ × ℕ) :=
  if h : ∃ Sig, BcGood D Rw σ Sig then Multiset.ofList (h.choose.map fun p => (p.a, p.d)) else {(D.R.r, 1)}

def RbarData {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (σ : D.what₂.FT) (lam : D.what₂.places.Pl) : Prop :=
  ∃ i : X.nd.Loc, X.nd.w i = lam ∧ ∃ (Sig : List (Formalism.BasicNotions.Part Y.naut.CG))
    (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)),
    HasParamW X.nd Y.naut i σ Sig ∧ IsRepOfSig X.nd Y.naut i Sig ρ


open Classical in
def rbarOf {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (σ : D.what₂.FT) (lam : D.what₂.places.Pl) :
    G D.host.E X.nd.Om →* GL (Fin D.R.r) (Fb (D.what₂.places.resChar lam) (D.what₂.places.resChar_prime lam)) :=
  if h : RbarData Y σ lam then
    ssRep (mapRep (((fbCast (h.choose_spec.1 ▸ X.nd.w_l h.choose).symm (X.nd.lPrime h.choose).out
        (D.what₂.places.resChar_prime lam)).toRingHom.comp
      ((Y.naut.kFbar h.choose).comp (IsLocalRing.residue (X.nd.O h.choose))))) h.choose_spec.2.choose_spec.choose)
  else 1

def mtSup {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (i : X.nd.Loc) (σ' : (lay0 D).ntypes.Par) :
    Submodule ℂ (D.what₂.Mt (X.nd.mu i) (X.nd.j i)) :=
  ⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = (lay0 D).ntypes.locPar σ' w) ∧
      IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P

def castMt {D : D7} {μ μ' : D.what₂.Tup} {j j' : ℕ} (h1 : μ = μ') (h2 : j = j') (M : Submodule ℂ (D.what₂.Mt μ j)) :
    Submodule ℂ (D.what₂.Mt μ' j') := by
  subst h1; subst h2; exact M


open Classical in
def mtParOf {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (μ : D.what₂.Tup) (j : ℕ) (σ' : (lay0 D).ntypes.Par) :
    Submodule ℂ (D.what₂.Mt μ j) :=
  if h : ∃ i, X.nd.mu i = μ ∧ X.nd.j i = j then castMt h.choose_spec.1 h.choose_spec.2 (mtSup Y h.choose σ') else ⊥

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceZeroPartConventionsChosenAgain
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3


set_option maxHeartbeats 1000000 in
theorem reFace_zero_parts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3), Pins R F cG → Holds R F → (∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) → ∃ kap lam err, Pins ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) cG ∧ Holds ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ ErrEq ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ kap = R.kap ∧ (∀ i t p v, R.EEp3 p ≠ ⊥ → lam i t p v = R.lam3 i t p v) ∧ ∃ (Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Y'.PW Y.PW ∧ HEq Y'.eE Y.eE ∧ HEq Y'.mj.eW Y.mj.eW ∧ HEq Z'.eRR Z.eRR ∧ HEq Z'.jW Z.jW := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Dc Sp Zsc hP hH hZ
  have h1 := pins_updS R F cG (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc) hP (scal_zeroLam R F Dc Sp Zsc hZ hP.char.scal)
  have h2 := prim_updS R F (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) hH.prim (zeroLam_pos R F (Zsc (R.toCx3 F).zs).l6m hH.prim.posScal.2)
    (thmB_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hZ hH.prim.thmB) (thmA_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hH.prim.thmA) (galD_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hH.prim.scalConj)
  have h3 := Holds.mk (reFace_prim (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc) h2)
    (further_face_statements_independent_of_error (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc) (furtherRows_updatedScalars R F (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) hH.aux)) hH.ok hH.sep
  have h4 := reFace_errEq (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc
  have h5 : ∀ i t p v, R.EEp3 p ≠ ⊥ → zeroLam R F (Zsc (R.toCx3 F).zs).l6m i t p v = R.lam3 i t p v :=
    fun i t p v hp => zeroLam_of_ne R F _ (hZ p hp i).1 fun hv => (hZ p hp i).2 v hv
  have h6 := read_updS_keep R F (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc)
    (XE_updS_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hP.char hH.prim hH.ok hH.sep hZ) X0 Y Z
  refine ⟨R.kap, (zeroLam R F (Zsc (R.toCx3 F).zs).l6m), (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc), ?_, ?_, ?_, rfl, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h1 :))
  · exact (by with_unfolding_all exact (h3 :))
  · exact (by with_unfolding_all exact (h4 :))
  · exact (by with_unfolding_all exact (h5 :))
  · exact (by with_unfolding_all exact (h6 :))

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionModPrimeLevelPrimeSmulEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.LvProj

open GlobalTheory.LvT.Pts
open Formalism.HermitianLatticesTheory (localization₂ dual)

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {M A : Submodule (𝓞 E) (Fin n → E)} {P : HeightOneSpectrum (𝓞 E)}

theorem redL_osmul (r : 𝓞 E) {x : Fin n → E} (hx : x ∈ localization₂ P.asIdeal M) :
    redL M P (r • x) = (Ideal.Quotient.mk P.asIdeal r : Res P) • redL M P x := by
  obtain ⟨s, hs, hx⟩ := (mem_locP P M _).1 hx
  refine redL_eq hs (by rw [smul_comm]; exact M.smul_mem _ hx) ?_
  rw [smul_comm, redL_spec hs hx, mk_smul_mk]
  congr 1
  exact Subtype.ext (smul_comm _ _ _)

omit [StarRing E] in
theorem redL_zero : redL M P 0 = 0 := redL_coe (M := M) (P := P) 0

def proj (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) : A →+ TDat.Red M P where
  toFun z := redL M P z.1
  map_zero' := redL_zero
  map_add' x y := redL_add (h ▸ le_locP P A x.2) (h ▸ le_locP P A y.2)

theorem proj_mk (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) (z : A) (hz : z.1 ∈ M) :
    proj h z = Submodule.Quotient.mk ⟨z.1, hz⟩ := redL_coe (M := M) (P := P) ⟨z.1, hz⟩

theorem proj_smul (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) (a : 𝓞 E) (z : A) :
    proj h (a • z) = (Ideal.Quotient.mk P.asIdeal a : Res P) • proj h z :=
  redL_osmul a (h ▸ le_locP P A z.2)

theorem proj_surj (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) : Function.Surjective (proj h) := by
  intro y
  obtain ⟨x, hx, rfl⟩ := redL_surj y
  have hx' : x ∈ localization₂ P.asIdeal M := le_locP P M hx
  obtain ⟨s, hs, hsx⟩ := (mem_locP P A x).1 (h ▸ hx')
  obtain ⟨t, p, hp, e⟩ := P.isMaximal.exists_inv hs
  refine ⟨⟨(t * s) • x, by rw [mul_smul]; exact A.smul_mem _ hsx⟩, ?_⟩
  show redL M P ((t * s) • x) = _
  have e2 : (Ideal.Quotient.mk P.asIdeal (t * s) : Res P) = 1 := by
    rw [← map_one (Ideal.Quotient.mk P.asIdeal), ← e, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 hp, add_zero]
  rw [redL_osmul _ hx', e2, one_smul]

theorem proj_ker (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) {J : Ideal (𝓞 E)} (hJ : J = P.asIdeal) (z : A) :
    proj h z = 0 ↔ z.1 ∈ J • A := by
  subst hJ
  show redL M P z.1 = 0 ↔ _
  constructor
  · intro h0
    obtain ⟨s, hs, hx⟩ := (mem_locP P M _).1 (h ▸ le_locP P A z.2)
    have h1 := redL_spec hs hx
    rw [h0, smul_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at h1
    have h2 := Submodule.mem_map_of_mem (f := M.subtype) h1
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at h2
    have key : P.asIdeal • M ≤ localization₂ P.asIdeal (P.asIdeal • A) := by
      rw [Submodule.smul_le]
      intro r hr y hy
      obtain ⟨t, ht, hty⟩ := (mem_locP P A y).1 (h ▸ le_locP P M hy)
      exact (mem_locP P _ _).2 ⟨t, ht, by rw [smul_comm]; exact Submodule.smul_mem_smul hr hty⟩
    obtain ⟨t, ht, h3⟩ := (mem_locP P _ _).1 (key h2)
    refine mem_smul_of_loc z.2 (s := t * s) (fun hm => (P.isPrime.mem_or_mem hm).elim ht hs) ?_
    rw [mul_smul]
    exact h3
  · intro hz
    have key : ∀ y ∈ P.asIdeal • A, y ∈ A ∧ redL M P y = 0 := by
      intro y hy
      refine Submodule.smul_induction_on hy (fun r hr w hw => ⟨A.smul_mem _ hw, ?_⟩) (fun y w hy hw => ⟨A.add_mem hy.1 hw.1, ?_⟩)
      · rw [redL_osmul r (h ▸ le_locP P A hw), Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_smul]
      · rw [redL_add (h ▸ le_locP P A hy.1) (h ▸ le_locP P A hw.1), hy.2, hw.2, add_zero]
    exact (key _ hz).2

end Red

section Dec

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem dualL_one (σ : E →+* E) (hσ : ∀ x, σ x = star x) {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1)
    (L : Submodule (𝓞 E) (Fin n → E)) : Formalism.L2.Forms.dualL σ J L = dual (hStd E n) L := by
  subst hJ
  have : Formalism.BasicNotions.dualSet σ (1 : Matrix (Fin n) (Fin n) E) L = (dual (hStd E n) L : Set (Fin n → E)) := by
    ext y
    rw [SetLike.mem_coe, Formalism.L2.Col.mem_dual]
    refine forall₂_congr fun x _ => ?_
    have e : Formalism.UG.hform σ (1 : Matrix (Fin n) (Fin n) E) x y = hStd E n x y := by
      show _ = ∑ i, star (x i) * y i
      unfold Formalism.UG.hform
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Matrix.one_apply, hσ]
    rw [e, Submodule.mem_one]
    rfl
  unfold Formalism.L2.Forms.dualL
  rw [this, Submodule.span_eq]

variable {d : Deco E n ST SG} {a : 𝓞 E}

theorem localization_L_eq_localization_dnN (hd : d.Ok) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) : localization₂ P.1.asIdeal d.L = localization₂ P.1.asIdeal (d.dnN P) := by
  rw [(hd.dnN_spec P hne).2.2.2]
  apply le_antisymm
  · refine localization_le_of_smul_mem (one_notMem P.1) fun x hx => ?_
    rw [one_smul]
    obtain ⟨h1, h2⟩ := (hd.mem_L x).1 hx
    exact (hd.mem_kerAt P x).2 ⟨h1, h2 P⟩
  · refine localization_le_of_le_localization _ fun x hx => ?_
    obtain ⟨h1, h2⟩ := (hd.mem_kerAt P x).1 hx
    exact (hd.mem_locP_L P x).2 ⟨le_locP _ _ h1, h2⟩

theorem sup_le_locP (hd : d.Ok) (ha : SepElt ST a) (P : ST) : d.L ⊔ P.1.asIdeal • d.Lsh ≤ localization₂ P.1.asIdeal d.L := by
  refine sup_le (le_locP _ _) ?_
  rw [Submodule.smul_le]
  intro r hr y hy
  have hy' := hd.Lsh_le_at ha P hy
  exact (hd.mem_locP_L P _).2 ⟨Submodule.smul_mem _ _ hy', by
    rw [hd.f_smul P r y hy', Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]⟩

theorem localization_Lsh_eq_localization_N (hd : d.Ok) (ha : SepElt ST a) (P : ST) {A : Submodule (𝓞 E) (Fin n → E)} (hA : A = d.Lsh) :
    localization₂ P.1.asIdeal A = localization₂ P.1.asIdeal d.N := hA ▸ hd.locP_Lsh ha P

theorem localization_sup_eq_localization_dnN (hd : d.Ok) (ha : SepElt ST a) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) {A : Submodule (𝓞 E) (Fin n → E)}
    (hA : A = d.L ⊔ P.1.asIdeal • d.Lsh) : localization₂ P.1.asIdeal A = localization₂ P.1.asIdeal (d.dnN P) := by
  subst hA
  rw [← localization_L_eq_localization_dnN hd P hne]
  exact le_antisymm (localization_le_of_le_localization _ (sup_le_locP hd ha P))
    (localization_le_of_smul_mem (one_notMem P.1) fun x hx => by rw [one_smul]; exact Submodule.mem_sup_left hx)

theorem f_eq_zero_iff (hd : d.Ok) (ha : SepElt ST a) (P : ST) {z : Fin n → E} (hz : z ∈ d.Lsh) :
    d.f P z = 0 ↔ z ∈ d.L ⊔ P.1.asIdeal • d.Lsh := by
  constructor
  · intro h0
    obtain ⟨s, hs, hsz⟩ := (mem_locP _ _ _).1 ((hd.mem_locP_L P z).2 ⟨hd.Lsh_le_at ha P hz, h0⟩)
    obtain ⟨t, p, hp, e⟩ := P.1.isMaximal.exists_inv hs
    have : z = t • (s • z) + p • z := by rw [← mul_smul, ← add_smul, e, one_smul]
    rw [this]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ t hsz) (Submodule.smul_mem_smul hp hz)
  · intro h
    exact ((hd.mem_locP_L P z).1 (sup_le_locP hd ha P h)).2

theorem reductionModPrime_levelPrime_smul_eq (hd : d.Ok) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) {q : 𝓞 E} (hq : q ∈ P.1.asIdeal) {z e : Fin n → E}
    (hz : z ∈ d.at P.1) (hfz : d.f P z = 1) (he : e ∈ d.N) (hfe : d.f P e = 1) (t : d.dnN P) (ht : t.1 = q • e) :
    redL (d.dnN P) P.1 (q • z) = Submodule.Quotient.mk t := by
  have he' : e ∈ d.at P.1 := le_locP _ _ he
  have hn : (-1 : 𝓞 E) • e ∈ d.at P.1 := Submodule.smul_mem _ _ he'
  have m : z + (-1 : 𝓞 E) • e ∈ localization₂ P.1.asIdeal (d.dnN P) := by
    rw [← localization_L_eq_localization_dnN hd P hne]
    refine (hd.mem_locP_L P _).2 ⟨Submodule.add_mem _ hz hn, ?_⟩
    rw [hd.f_add P _ hz _ hn, hd.f_smul P _ _ he', hfz, hfe, map_neg, map_one]
    ring
  have e1 : q • z = q • (z + (-1 : 𝓞 E) • e) + t.1 := by
    rw [ht, neg_one_smul, ← smul_add, neg_add_cancel_right]
  rw [e1, redL_add (Submodule.smul_mem _ _ m) (le_locP _ _ t.2), redL_osmul _ m,
    Ideal.Quotient.eq_zero_iff_mem.2 hq, zero_smul, zero_add, redL_coe]

end Dec

section TD

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ}

theorem fv_mk (hl : A.Laws T) (P : ST) (c : S.Cl) (x : A.N c.1 (S.rep c)) :
    A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  have h0 := hl.fv_ne P c
  unfold TDat.fv at h0 ⊢
  split_ifs at h0 ⊢ with h1
  · exact h1.choose_spec x
  · exact absurd rfl h0

theorem te_mk (hl : A.Laws T) (P : ST) (c : S.Cl) :
    ∃ t : A.dnN c.1 (S.rep c) P, (∃ e ∈ A.N c.1 (S.rep c), A.f c.1 (S.rep c) P e = 1 ∧ (t : Fin n → E) = (T : 𝓞 E) • e) ∧
      Submodule.Quotient.mk t = A.te T P c := by
  have h0 := hl.te_ne P c
  unfold TDat.te at h0 ⊢
  split_ifs at h0 ⊢ with h1
  · exact ⟨h1.choose, h1.choose_spec, rfl⟩
  · exact absurd rfl h0

end TD

end GlobalTheory.Mem.Col2.LvProj

end


open GlobalTheory.Mem.Col2.LvProj GlobalTheory.LvT.Pts in
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Mem.Col2.TC.exists_level_projections : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∃ (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.IdL l Z u a i hi L := by
  intro B X I hI hP l Z u a i hi
  obtain ⟨-, -, -, hc⟩ := TC.spaces_in_coordinates I hI hP l Z
  obtain ⟨hg, -, hc⟩ := hc i hi
  have hL := (hc u a).1
  clear hc
  have ha := sepElt_of_ok l.pr u
  have hne : ∀ v : (B.primes X).vT u, conjPrime₂ v.1 ≠ v.1 := fun v => (moveHyp_of_ok l.pr u v).ne
  have hT : ∀ v : (B.primes X).vT u, ((B.T u : ℕ) : 𝓞 B.fields.E) ∈ v.1.asIdeal := fun v => Formalism.L2.Col.T_mem l.pr u v
  have hl := (l.fmL u a).lev i
  let d : (I.stp u a i).Cl → Deco B.fields.E (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs :=
    fun c => ((I.stp u a i).rep c).1.1.deco.1
  have hd : ∀ c, (d c).Ok := fun c => ((I.stp u a i).rep c).1.1.deco.2
  have hs : ∀ x : B.fields.E, (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) x = star x := fun _ => rfl
  have hD0 := fun L => @dualL_one B.fields.E B.fields.fieldE B.fields.nfE B.fields.starE _ _ hs _ hg L
  have hD : ∀ c, LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) = (d c).Lsh := fun c =>
    (hD0 _).trans (congrArg _ (hL c))
  have hPv : ∀ v : (B.primes X).vT u, PvG (D := I.rec7 l Z) (I.resT l u a) v = v.1.asIdeal := fun v =>
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem (I := (v.1.asIdeal : Ideal (𝓞 B.fields.E)))
  have hK : ∀ (v : (B.primes X).vT u) c, LkG (I.rec7 l Z) i hi (PvG (D := I.rec7 l Z) (I.resT l u a) v)
      (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) = (d c).L ⊔ v.1.asIdeal • (d c).Lsh := fun v c =>
    congrArg₂ (· ⊔ ·) (hL c) (congrArg₂ (· • ·) (hPv v) (hD c))
  have h1 := fun v c => localization_Lsh_eq_localization_N (hd c) ha v (hD c)
  have h2 := fun v c => localization_sup_eq_localization_dnN (hd c) ha v (hne v) (hK v c)
  have hf : ∀ v c z, (I.fm l u a).fv i v c (proj (h1 v c) z) = (d c).f v z.1 := fun v c z =>
    dual_redL ((hd c).f_smul v) _ (fv_mk hl v c) (h1 v c ▸ le_locP v.1 _ z.2)
  refine ⟨⟨fun v c => proj (h1 v c), fun v c => proj_surj (h1 v c), fun v c => proj_smul (h1 v c),
    fun v c => proj_ker (h1 v c) (hPv v), fun v c z => ?_, fun v c => proj (h2 v c), fun v c => proj_surj (h2 v c),
    fun v c => proj_smul (h2 v c), fun v c => proj_ker (h2 v c) (hPv v), fun v c z hz h => ?_⟩,
    fun v c z h => proj_mk (h1 v c) z h, fun v c z h => proj_mk (h2 v c) z h⟩
  · have e := f_eq_zero_iff (hd c) ha v (z := z.1) (hD c ▸ z.2)
    rw [← hK v c, ← hf v c z] at e
    exact e
  · obtain ⟨t, ⟨e, he, hfe, ht⟩, hte⟩ := te_mk hl v c
    exact (reductionModPrime_levelPrime_smul_eq (hd c) v (hne v) (hT v) ((hd c).Lsh_le_at ha v (hD c ▸ z.2)) ((hf v c z).symm.trans hz) he hfe t ht).trans hte
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldEquivRealSubfieldQuotientTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ResF

variable {D : D7} {u : D.what₂.Word}

theorem conj_conj_host (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply]
  simp

theorem exists_intF (z : 𝓞 D.host.E) (hz : D.host.conj (z : D.host.E) = z) :
    ∃ zF : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF = z := by
  have hF : (z : D.host.E) ∈ D.host.F := (D.host.conjE_mem_hostF_iff _).2 hz
  refine ⟨⟨⟨z, hF⟩, ?_⟩, ?_⟩
  · exact (isIntegral_algHom_iff (D.host.F.subtype.toIntAlgHom) Subtype.val_injective).mp
      (RingOfIntegers.isIntegral_coe z)
  · rfl

theorem res_algebraMap_surjective (A : AtTTied u) (v : (D.mem u).A.vT) :
    Function.Surjective ((A.res v).comp (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) := by
  intro r
  obtain ⟨y, rfl⟩ := A.res_surj v r
  let cO : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv
  have hcO : ∀ y : 𝓞 D.host.E, ((cO y : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E) := fun y => rfl
  obtain ⟨t, ht⟩ := exists_intF (D := D) (A.piU + cO A.piU) (by
    push_cast; simp only [hcO, map_add (f := _), conj_conj_host]; ring)
  obtain ⟨z, hz⟩ := exists_intF (D := D) (y * cO A.piU + cO y * A.piU) (by
    push_cast; simp only [hcO, map_add (f := _), map_mul, conj_conj_host]; ring)
  have htp : t ∉ (A.eV v).1.asIdeal := by
    rw [A.res_v, ht, map_add (f := _), A.res_pi, zero_add]; exact A.res_conj v _ rfl
  obtain ⟨s, i, hi, hsi⟩ := ((A.eV v).1.isMaximal).exists_inv htp
  have hi0 : A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) i) = 0 := (A.res_v v i).1 hi
  have hst : A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s) * A.res v (cO A.piU) = 1 := by
    have := congrArg (fun x => A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x)) hsi
    simp only [map_add (f := _), map_mul, map_one, hi0, add_zero, ht, A.res_pi, zero_add] at this
    exact this
  refine ⟨s * z, ?_⟩
  simp only [RingHom.comp_apply, map_mul, hz, map_add (f := _), A.res_pi, mul_zero, add_zero]
  rw [mul_comm (A.res v y), ← mul_assoc, hst, one_mul]

theorem exists_fv_equiv (A : AtTTied u) (v : (D.mem u).A.vT) :
    ∃ e : (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (A.eV v).1.asIdeal),
      ∀ a : 𝓞 D.host.F, e (A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a)) = Ideal.Quotient.mk _ a := by
  have hker : (A.eV v).1.asIdeal = RingHom.ker ((A.res v).comp (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) := by
    ext x; rw [RingHom.mem_ker]; exact A.res_v v x
  refine ⟨((Ideal.quotEquivOfEq hker).trans
    (RingHom.quotientKerEquivOfSurjective (res_algebraMap_surjective A v))).symm, fun a => ?_⟩
  rw [RingEquiv.symm_apply_eq]
  rfl

theorem fv_equiv_quot : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X),
    ColIn.Ok I → TC.Pins B X →
    ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (u : B.Word)
      {Ch : ℕ → Type} {chOf : ∀ i, ((TC.rec7 I l Z).mem u).C.cls i → Ch i}
      (F : Formalism.L2.Forms.FormsTiedSym (TC.rec7 I l Z) u Ch chOf),
      TC.StdF I l Z u F → ∀ v : ((TC.rec7 I l Z).mem u).A.vT,
      ∃ e : ((TC.rec7 I l Z).mem u).A.Fv v ≃+* (𝓞 (TC.rec7 I l Z).host.F ⧸ (F.atT.eV v).1.asIdeal),
        ∀ a : 𝓞 (TC.rec7 I l Z).host.F,
          e (F.atT.res v (algebraMap (𝓞 (TC.rec7 I l Z).host.F) (𝓞 (TC.rec7 I l Z).host.E) a)) =
            Ideal.Quotient.mk _ a := by
  intro B X I _ _ l Z u Ch chOf F _ v
  exact exists_fv_equiv F.atT v

end GlobalTheory.Mem.Col2.ResF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLevelFormsSpanDefiniteMultiplicitySpace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.TopSpan

theorem span_range_map_mem {M N ι : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (f : M →ₗ[ℂ] N)
    (g : ι → M) {y : M} (hy : y ∈ Submodule.span ℂ (Set.range g)) : f y ∈ Submodule.span ℂ (Set.range fun i => f (g i)) := by
  have h := Submodule.mem_map_of_mem (f := f) hy
  rwa [Submodule.map_span, ← Set.range_comp] at h


set_option maxHeartbeats 1000000 in
theorem topSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → A.fam.Ok 1 → TopMultH R → ∀ (b : Bool) (t : T), Submodule.span ℂ (Set.range fun x => R.cX.toMap R.prX ((R.HX t).e (R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)))) = Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB hPr hOk hTop b t
  have hjX : ∀ x, (R.HX t).e (R.jX t x) = R.B.jR t x := hB.models.jX t
  simp only [hjX]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hmem : R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x) ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ
        (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ :=
      Bridge.ClassPres.extMem_holds (R.B.R t).pres _
    have hlv := (GlobalTheory.T.levelCharacterSpace_coords_iff_level_acts_by_char _ _ _ (A.fam.R t).r (F.lvl b).P (F.lvl b).ψ (rowForm A (F.lvl b).P (F.lvl b).ψ t x)).1 ⟨x, rfl⟩
    exact _root_.GlobalTheory.DefiniteMult.toMap_mem_levP D G Pl0 T A Ks R F hB b t _ hmem (GlobalTheory.TopSpan.jR_level D G Pl0 T A Ks R F b t _ hlv)
  · intro Tm hT
    obtain ⟨Fn, hF, hQ, rfl⟩ := _root_.GlobalTheory.MultLevelP.exists_form_of_mult D G Pl0 T A Ks R F hB b t Tm hT
    exact span_range_map_mem (R.cX.toMap R.prX) (fun x => R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x))
      (_root_.GlobalTheory.TopSpan.proj_span D G Pl0 T A Ks R F b t Fn hF hQ)

end GlobalTheory.TopSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralRedivisionTermEquivKeepsTermDataStatement
section
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ t : RT Y u u', (Formalism.L2.SG.FourParts.termIsId t ↔ Formalism.L2.SG.FourParts.termIsId (eRT Z Y u u' t)) ∧ (Formalism.L2.SG.FourParts.termInS t ↔ Formalism.L2.SG.FourParts.termInS (eRT Z Y u u' t)) ∧ (t.relevant ↔ (eRT Z Y u u' t).relevant) ∧ (t.FeqF ↔ (eRT Z Y u u' t).FeqF) ∧ (t.generic ↔ (eRT Z Y u u' t).generic) ∧ t.G = (eRT Z Y u u' t).G ∧ (∀ p, Formalism.L2.SG.Saturated.termBBne t p ↔ Formalism.L2.SG.Saturated.termBBne (eRT Z Y u u' t) p) ∧ Formalism.L2.SG.PairVal.ptOf t = Formalism.L2.SG.PairVal.ptOf (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.massTerm t = Formalism.L2.SG.PairVal.massTerm (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t = Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) (reY Z Y).δ (reY Z Y).M) (eRT Z Y u u' t)) ∧ ∀ w, Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w = Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w := by
  first | exact @GlobalTheory.Mem.SRe.eRT_keeps_term_data | exact GlobalTheory.Mem.SRe.eRT_keeps_term_data | (intros; apply GlobalTheory.Mem.SRe.eRT_keeps_term_data <;> assumption)
end

