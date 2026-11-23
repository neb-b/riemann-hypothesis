module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0805
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0801
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0297
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0299
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormReadingEqGoodModelVectorEvaluation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.SeriesTie.ModelGood

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)

def jH (j : Fin D.R.m) : S.WL ((j : ℕ) + 1) →+ (Rl.HW j (sg0 D A3.A)).H where
  toFun x := (Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e x)
  map_zero' := by rw [map_zero, map_zero]
  map_add' x y := by rw [map_add (f := _), map_add (f := _)]

theorem jH_smul (j : Fin D.R.m) (c : D.what₂.LL) (x : S.WL ((j : ℕ) + 1)) :
    jH YS j (c • x) = D.what₂.embLL c • jH YS j x := by
  change (Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e (c • x)) = _
  rw [map_smul, map_smulₛₗ, show sg0 D A3.A c = D.what₂.embLL c from
    congrArg (fun f : D.what₂.LL →+* ℂ => f c) (sgAt_mk _ Rl.hv0)]
  rfl

section Read

variable {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

def evH : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1) →+ (Rl.HW j (sg0 D A3.A)).H :=
  TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ρ.e i b a)).comp
        ((jH YS j).comp (S.A ((j : ℕ) + 1)).WK.subtype.toAddMonoidHom)
      map_zero' := by ext; simp [show ρ.e i b (0 : NX.KB S i b) = 0 from map_zero _]
      map_add' := fun x y => by
        ext; simp [show ρ.e i b (x + y : NX.KB S i b) = ρ.e i b x + ρ.e i b y from map_add _ _ _, add_smul] }
    fun c a f => by
      change ρ.e i b (sideEmb D.ntw i b (S.kKs c) * (show FractionRing (D.ntw.O i) from a)) • jH YS j (Subtype.val f) =
        ρ.e i b a • jH YS j (c • Subtype.val f)
      rw [← algebraMap_smul D.what₂.LL c, jH_smul, map_mul, hρ.e_LL0, smul_smul, mul_comm, ← S.kKs_spec]
      rfl

theorem evH_tmul (a : NX.KB S i b) (f : NX.FmK S ((j : ℕ) + 1)) :
    evH YS hρ i j b (a ⊗ₜ f) = ρ.e i b a • jH YS j (Subtype.val f) := rfl

theorem evK_eq (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (t : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    evK YS v₀ hρ i j b t = (Rl.HW j (sg0 D A3.A)).e (evH YS hρ i j b t) (v₀ j _) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]; rfl
  | tmul a f => rw [evK_tmul, evH_tmul, map_smul]; rfl

theorem evH_smul (c : NX.KB S i b) (t : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    evH YS hρ i j b (c • t) = ρ.e i b c • evH YS hρ i j b t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | tmul a f =>
    rw [TensorProduct.smul_tmul', evH_tmul, evH_tmul, smul_smul]
    exact congrArg (· • _) (map_mul (ρ.e i b) c a)

def mv (y : D.nexp.Fm i ((j : ℕ) + 1) b) : (Rl.HW j (sg0 D A3.A)).H :=
  evH YS hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 y)

theorem mv_act (hU : Rl.toRealDat.LUnif) (g : G0g D.nd) (y : D.nexp.Fm i ((j : ℕ) + 1) b) :
    (Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b (D.nexp.actG i _ b g y)) =
      postOn _ (actL (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (cG.symm g))
        ((Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b y)) := by
  unfold mv
  rw [YS.act]
  generalize YS.eF i _ b (Nat.le_add_left _ _) j.2 y = t
  induction t using TensorProduct.induction_on with
  | zero =>
    erw [LinearEquiv.map_zero]
    simp only [map_zero]
    exact (congrArg (Rl.HW j (sg0 D A3.A)).e ((evH YS hρ i j b).map_zero)).trans (map_zero _)
  | add y z hy hz => erw [LinearEquiv.map_add, map_add, map_add, hy, hz, map_add, map_add, map_add]
  | tmul a f0 =>
    have e1 : (NX.actG S i ((j : ℕ) + 1) b (YS.rho _ (Nat.le_add_left _ _) j.2) (YS.chi _ (Nat.le_add_left _ _) j.2) g)
        (a ⊗ₜ f0) = ((NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g)))⁻¹ * a) ⊗ₜ
          (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0) := by
      change (NX.readLL0 S i b (NX.chiL S _ _ (S.eG.symm g)))⁻¹ •
        (a ⊗ₜ[S.Ks] (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0)) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul]
    erw [e1]
    rw [evH_tmul, evH_tmul]
    have hgeq : Rl.eG ((YS.fi j).eG (S.eG.symm g)) = cG.symm g := by
      have h0 := YS.geq j (S.eG.symm g)
      rw [MulEquiv.apply_symm_apply] at h0
      exact ((MulEquiv.symm_apply_eq cG).2 h0.symm).symm
    have he : ρ.e i b (NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g))) =
        D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) :=
      hρ.e_LL0 i b _
    have hne : D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) ≠ 0 :=
      (map_ne_zero _).2 (Units.ne_zero _)
    have hs : sg0 D A3.A = D.what₂.embLL := GlobalTheory.SeriesTie.ActProof.sg0_eq_embLL Rl
    change (Rl.HW j (sg0 D A3.A)).e (ρ.e i b _ • (Rl.FW j).j (sg0 D A3.A)
      ((YS.fi j).e ((S.A ((j : ℕ) + 1)).ρ (S.eG.symm g) (Subtype.val f0)))) = _
    rw [map_smul, map_smul, map_smul, (YS.fi j).rho, (hU j _).2.2, (YS.fi j).chi, hgeq, smul_smul]
    congr 1
    erw [map_mul, map_inv₀, he, hs]
    field_simp

theorem mv_smul (c : FractionRing (D.ntw.O i)) (y : D.nexp.Fm i ((j : ℕ) + 1) b) :
    mv YS hρ i j b (c • y) = ρ.e i b c • mv YS hρ i j b y := by
  unfold mv
  rw [map_smul]
  exact evH_smul YS hρ i j b c _

theorem mv_sum {ι : Type} (s : Finset ι) (y : ι → D.nexp.Fm i ((j : ℕ) + 1) b) :
    mv YS hρ i j b (∑ k ∈ s, y k) = ∑ k ∈ s, mv YS hρ i j b (y k) := by
  unfold mv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact map_sum (evH YS hρ i j b) _ _

theorem postOn_eWf_sum (σ : D.what₂.LL →+* ℂ) (M : MMap (Rl.MW j σ)) :
    postOn (Rl.MW j σ) (Rl.toRealDat.eWf j σ) M = ∑ γ : Γ, RealDat.eC (A := A3.A) σ γ •
      postOn (Rl.MW j σ) (actL (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG γ)) M := by
  refine MultilinearMap.ext fun v => ?_
  simp only [RealDat.eWf, gaL, postOn, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.compMultilinearMap_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply, MultilinearMap.smul_apply]
  rfl

theorem mv_eG (hU : Rl.toRealDat.LUnif)
    (hid : ∀ γ : Γ, D.what₂.embLL ((idemOf A3.A.X).coeff γ) = D.ntypes.e0.coeff ((Rl.eG.trans cG) γ))
    (y : D.nexp.Fm i ((j : ℕ) + 1) b) :
    (Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b y)) =
      postOn _ (Rl.toRealDat.eWf j (sg0 D A3.A)) ((Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b y)) := by
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv Γ (Rl.eG.trans cG).toEquiv
  have h1 : Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b y = ∑ g, (D.nexp.eAlg i b).coeff g • D.nexp.actG i _ b g y := by
    unfold Formalism.MainNotions.IntegralHeckeForms.eG
    rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype]
    · rw [LinearMap.sum_apply]; rfl
    · intro; exact zero_smul _ _
  have hc : ∀ g, ρ.e i b ((D.nexp.eAlg i b).coeff g) = D.ntypes.e0.coeff g := fun g => by
    have h : (D.nexp.eAlg i b).coeff g = NX.readLL0 S i b (D.nexp.eLL0 g) := by rw [D.nexp.eAlg_def]; rfl
    rw [h]
    exact (hρ.e_LL0 i b _).trans (D.nStage_trivialCharacter_coeff_eq g)
  have hs : sg0 D A3.A = D.what₂.embLL := GlobalTheory.SeriesTie.ActProof.sg0_eq_embLL Rl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, mv_sum, map_sum, postOn_eWf_sum]
  refine (Fintype.sum_equiv (Rl.eG.trans cG).toEquiv _ _ fun γ => ?_).symm
  rw [mv_smul, map_smul, mv_act YS hρ i j b hU, hc]
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  congr 1
  exact (congrArg (fun f : D.what₂.LL →+* ℂ => f ((idemOf A3.A.X).coeff γ)) hs).trans (hid γ)

end Read
end GlobalTheory.SeriesTie.ModelGood

open GlobalTheory.SeriesTie.ModelGood in
theorem GlobalTheory.SeriesTie.rd_good_model : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∃ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.goodModel X.R.toRealDat j,
      Y.Z.rd i j b x = (Y.Z.ν i j b)⁻¹ • (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) := by
  intro D X E Y i j b x hx
  obtain ⟨f, -, rfl⟩ := hx
  have hidem : ∀ z, Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b z) = Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i ((j : ℕ) + 1) b z :=
    fun z => by rw [← Module.End.mul_apply, Formalism.MainNotions.IntegralHeckeForms.eG, ← map_mul, D.nexp.eAlg_idem]
  refine ⟨mv Y.YS Y.Z.good i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b f), ⟨?_, ?_⟩, ?_⟩
  · have h := LinearMap.mem_range_self (X.R.HW j (sg0 D X.A3.A)).e
      (mv Y.YS Y.Z.good i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b f))
    rw [(X.char.models.HW j _).2.1] at h
    exact h
  · rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply]
    rw [← mv_eG Y.YS Y.Z.good i j b X.unif X.idem, hidem]
  · change (Y.Z.ν i j b)⁻¹ • evK Y.YS X.geo.v₀ Y.Z.good i j b _ = _
    exact congrArg _ (evK_eq Y.YS Y.Z.good i j b X.geo.v₀ _)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartEigensystemIsTripleEigensystem
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.EigAll

theorem exists_smul_mem_of_mem_span {O K V : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (N : Submodule O V)
    {v : V} (hv : v ∈ Submodule.span K (N : Set V)) : ∃ d : O, d ≠ 0 ∧ d • v ∈ N := by
  let S : Submodule K V :=
    { carrier := {v | ∃ d : O, d ≠ 0 ∧ d • v ∈ N}
      add_mem' := by
        rintro a c ⟨d, hd, ha⟩ ⟨e, he, hc⟩
        refine ⟨d * e, mul_ne_zero hd he, ?_⟩
        rw [smul_add]
        refine N.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact N.smul_mem _ ha
        · rw [mul_smul]; exact N.smul_mem _ hc
      zero_mem' := ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩
      smul_mem' := by
        rintro c a ⟨d, hd, ha⟩
        obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := O) c
        have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
        have hmK : algebraMap O K m ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
        refine ⟨m * d, mul_ne_zero hm0 hd, ?_⟩
        have e1 : m • ((algebraMap O K n / algebraMap O K m) • a) = n • a := by
          rw [← algebraMap_smul K m, smul_smul, mul_div_cancel₀ _ hmK, algebraMap_smul]
        show (m * d) • ((algebraMap O K n / algebraMap O K m) • a) ∈ N
        rw [mul_comm, mul_smul, e1, smul_comm]
        exact N.smul_mem _ ha }
  have hle : Submodule.span K (N : Set V) ≤ S :=
    Submodule.span_le.2 fun x hx => ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  exact hle hv

theorem eq_zero_of_joint {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : ι → V →ₗ[K] V) (p : ι → Prop) (ev : ι → K) (M : Finset (ι → K)) :
    ∀ y : V, (∀ μ ∈ M, ∃ t, p t ∧ μ t ≠ ev t) → (∀ t, p t → T t y = ev t • y) →
      y ∈ Submodule.span K {z | ∃ μ ∈ M, ∀ t, p t → T t z = μ t • z} → y = 0 := by
  classical
  induction M using Finset.induction_on with
  | empty =>
    intro y _ _ hs
    have : {z : V | ∃ μ ∈ (∅ : Finset (ι → K)), ∀ t, p t → T t z = μ t • z} = ∅ := by
      ext z; simp
    rw [this, Submodule.span_empty, Submodule.mem_bot] at hs
    exact hs
  | insert μ0 M _ ih =>
    intro y hne hy hs
    obtain ⟨t0, hp0, hμ0⟩ := hne μ0 (Finset.mem_insert_self _ _)
    let L : V →ₗ[K] V := T t0 - μ0 t0 • LinearMap.id
    have hL : Submodule.span K {z | ∃ μ ∈ insert μ0 M, ∀ t, p t → T t z = μ t • z} ≤
        (Submodule.span K {z | ∃ μ ∈ M, ∀ t, p t → T t z = μ t • z}).comap L := by
      rw [Submodule.span_le]
      rintro z ⟨μ, hμ, hz⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      rcases Finset.mem_insert.1 hμ with rfl | hμ
      · have : L z = 0 := by
          simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hz t0 hp0, sub_self]
        rw [this]; exact Submodule.zero_mem _
      · have : L z = (μ t0 - μ0 t0) • z := by
          simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hz t0 hp0, sub_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, hμ, hz⟩)
    have hLy : L y = (ev t0 - μ0 t0) • y := by
      simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hy t0 hp0, sub_smul]
    have h0 := ih ((ev t0 - μ0 t0) • y) (fun μ hμ => hne μ (Finset.mem_insert_of_mem hμ))
      (fun t ht => by rw [map_smul, hy t ht, smul_comm]) (hLy ▸ hL hs)
    rcases smul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hμ0
    · exact h

variable {D : D7} {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
  {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
  {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}


open Classical in
def trEig (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Set (D.nexp.Fm i j b) :=
  {z | ∃ μ ∈ (Finset.univ.filter fun s : D.ntw.Sig i => D.ntw.jS i s = j ∧ D.ntw.side i s = b).image
      (fun s (t : ℕ × PlE D.host) => GlobalTheory.EigTie.sigEv s t.1 t.2),
    ∀ t : ℕ × PlE D.host, HkIdx i t.1 t.2 → D.nexp.hkF i j b t.1 t.2 z = μ t • z}

theorem good_part_le_span_triple_eigenvectors (Bs : SideB D cf Rw low Pq S hL eig θ) (hF : FullAll D) (i : D.ntw.Tw) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) :
    V0 D.nexp i j b ≤ Submodule.span (FractionRing (D.ntw.O i)) (trEig D i j b) := by
  classical
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  set K := FractionRing (D.ntw.O i)
  let Φ : K ⊗[D.ntw.O i] D.ntw.B i j b →ₗ[K] D.nexp.Fm i j b := (D.nexp.embB i j b).liftBaseChange K
  have hΦ : ∀ k P, HkIdx i k P → ∀ z, Φ (((D.ntw.hk i j b k P).baseChange K) z) = D.nexp.hkF i j b k P (Φ z) := by
    intro k P hP z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [Φ, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, map_smul]
      rw [Bs.hk_emb i j b k P x h1 h2 hP.2.2.2 hP.2.2.1 hP.2.1]
    | add z w hz hw => simp only [map_add (f := _), hz, hw]

  have hrange : ∀ x : D.ntw.B i j b, D.nexp.embB i j b x ∈ Submodule.span K (trEig D i j b) := by
    intro x
    have hx : (1 : K) ⊗ₜ[D.ntw.O i] x ∈ (⊤ : Submodule K (K ⊗[D.ntw.O i] D.ntw.B i j b)) := trivial
    rw [← Bs.sigSpan i j b h1 h2] at hx
    have hx' := Submodule.mem_map_of_mem (f := Φ) hx
    rw [Submodule.map_span] at hx'
    have e : Φ ((1 : K) ⊗ₜ[D.ntw.O i] x) = D.nexp.embB i j b x := by
      show (D.nexp.embB i j b).liftBaseChange K ((1 : K) ⊗ₜ[D.ntw.O i] x) = _
      rw [LinearMap.liftBaseChange_tmul, one_smul]
    rw [e] at hx'
    refine Submodule.span_mono ?_ hx'
    rintro _ ⟨z, ⟨s, hs1, hs2, hz⟩, rfl⟩
    refine ⟨fun t => GlobalTheory.EigTie.sigEv s t.1 t.2, Finset.mem_image.2 ⟨s, by simp [hs1, hs2], rfl⟩, ?_⟩
    intro t ht
    rw [← hΦ t.1 t.2 ht, hz t.1 t.2 ht.1 ht.2.1 ht.2.2.1 ht.2.2.2, map_smul]
    rfl
  intro v hv
  obtain ⟨d, hd, hdv⟩ := exists_smul_mem_of_mem_span (K := K) (D.nexp.Bsup i j b) (by rw [hF i j hj b]; trivial)
  have hdV : d • v ∈ V0 D.nexp i j b := by
    rw [← algebraMap_smul K d v]; exact Submodule.smul_mem _ _ hv
  have hmem : d • v ∈ LinearMap.range (D.nexp.embB i j b) := by
    rw [Bs.tw.B_range i j b]; exact ⟨hdv, hdV⟩
  obtain ⟨x, hx⟩ := hmem
  have hdK : algebraMap (D.ntw.O i) K d ≠ 0 := by
    intro h; exact hd (IsFractionRing.injective (D.ntw.O i) K (h.trans (map_zero _).symm))
  have : v = (algebraMap (D.ntw.O i) K d)⁻¹ • (d • v) := by
    rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hdK, one_smul]
  rw [this, ← hx]
  exact Submodule.smul_mem _ _ (hrange x)

theorem sig_all_of_sideB : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ),
    NoFormsOff D → MeetsAll D → CommAll D → FullAll D → D.nexp.sig_all := by
  intro D cf Rw low Pq S hL eig θ Bs hN hM hC hF
  classical
  refine EigModel.sig_all_of hN hM hC ?_
  rintro i j hj b ev ⟨y, hyV, hy0, hyE⟩
  by_contra hno
  push_neg at hno
  apply hy0
  refine eq_zero_of_joint (fun t : ℕ × PlE D.host => D.nexp.hkF i j b t.1 t.2) (fun t => HkIdx i t.1 t.2)
    (fun t => ev t.1 t.2) _ y ?_ (fun t ht => hyE t.1 t.2 ht) (good_part_le_span_triple_eigenvectors Bs hF i j hj b hyV)
  intro μ hμ
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hμ
  obtain ⟨hs1, hs2⟩ := (Finset.mem_filter.1 hs).2
  obtain ⟨k, P, hk, hne⟩ := hno s hs1 hs2
  exact ⟨(k, P), hk, hne⟩

end GlobalTheory.TwInputs.EigAll

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTwistDetCharEqOneOfSupportedTypePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistTypeDet


open Classical in
theorem detChar_eq_one_of_suppAt : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (A : Type) [CommGroup A] (t : Twist D A), t.Good → B.admitted t.Q → ∀ (u : G0 B.G.Pg T.rank) (κ : GA D T), Lev.IsLevelLift T B.F.βT B.G.levT u κ → SuppAt (idem B.G.Pg) T κ → detChar T t.chi κ = 1 := by
  intro D S T B hB _ A _ t ht hadm u κ hlift hsupp
  have hst : Lev.finE T κ ∈ St B.F.βT := Formalism.L2.DIV.parLev_St hlift.2.1
  rw [GlobalTheory.TwistDetStabAll.detChar_eq_prod_res B hB t ht hlift.1 hst]
  refine Finset.prod_eq_one fun PP hPP => ?_
  obtain ⟨P, hPg, hQ, hsplit⟩ := hadm.1.split
  have hnot : PP ∉ B.G.Pg := fun h => Finset.disjoint_left.mp hadm.1.disj h (Finset.mem_union_right _ hPP)
  rw [GlobalTheory.ExportSeries.redFn_eq_one_of_suppAt B.F.βT hsplit hPg (hQ (Finset.mem_union_right _ hPP)) hnot hst hsupp,
    map_one, map_one]

end GlobalTheory.TwistTypeDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypeFormReadingRightTranslateLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TypeRead

theorem actG_eG (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (u : G0g D.nd) (y : D.nexp.Fm i j b) :
    D.nexp.actG i j b u (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b y) = Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b (D.nexp.actG i j b u y) := by
  have h := congrArg (fun z => MonoidAlgebra.lift (FractionRing (D.ntw.O i)) (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)) z y)
    (D.nexp.eAlg_central i b (MonoidAlgebra.single u 1))
  simp only [map_mul, MonoidAlgebra.lift_single, one_smul, Module.End.mul_apply] at h
  exact h.symm

theorem finite_group_acts_on_good_type_form_by_character (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (x : D.nexp.Fm i j b) (hx : x ∈ V0 D.nexp i j b)
    (u : G0g D.nd) (hu : u ∈ D.nexp.U) :
    D.nexp.actG i j b u x = ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • x := by
  obtain ⟨f, hf, rfl⟩ := hx
  have hf' := (Submodule.mem_iInf _).1 hf ⟨u, hu⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hf'
  rw [actG_eG]
  change Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b ((D.nexp.actG i j b (⟨u, hu⟩ : D.nexp.U) : _ ≃ₗ[_] _) f) = _
  erw [hf']
  simp

end GlobalTheory.TypeRead


open GlobalTheory.TypeRead in
theorem GlobalTheory.TypeRead.rd_mul_lift : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
      Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
      Y.Z.rd i j b x (g * κ) = Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
        Y.Z.rd i j b x g := by
  intro D X E Y i j b x hx u hu κ hκ g
  have hA : ActRead (Y.Z.rd i j b) :=
    actRead_realRd D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _ Y.Z.pin X.unif
      X.char.models.HW
  rw [← hA u κ hκ x g, finite_group_acts_on_good_type_form_by_character D i _ b x hx u hu, map_smulₛₗ]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharUnramifiedOutsideOfLPowerGaloisCharStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unramified_outside_of_lPower_galois_char : ∀ (D : D7) (N : NData D.R D.host D.what₂) (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E N.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (r : G D.host.E N.Om →* ℂˣ) (l n : ℕ), l.Prime → (∀ σ, r σ ^ (l ^ n) = 1) → ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → GlobalTheory.ToricDistribution.Corr art r χ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, r σ = 1) → GlobalTheory.ExportSeries.UnramOutside c Q := by
  first | exact @GlobalTheory.UnramPull.unramOutside_of_corr | exact GlobalTheory.UnramPull.unramOutside_of_corr | (intros; apply GlobalTheory.UnramPull.unramOutside_of_corr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharUnramifiedOutsideSplitSetOfTameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unramified_outside_split_set_of_tame : ∀ (D : D7) (N : NData D.R D.host D.what₂) (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E N.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (r : G D.host.E N.Om →* ℂˣ) (M : ℕ), M ≠ 0 → (∀ σ, r σ ^ M = 1) → ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → GlobalTheory.ToricDistribution.Corr art r χ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ∀ P' : Pl D.host.E, (P' = P ∨ Formalism.BasicNotions.IsConjPl D.host P P') → χ.TameAt P') → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, r σ = 1) → GlobalTheory.ExportSeries.UnramOutside c Q := by
  first | exact @GlobalTheory.UnramTame.unramOutside_of_corr_of_tame | exact GlobalTheory.UnramTame.unramOutside_of_corr_of_tame | (intros; apply GlobalTheory.UnramTame.unramOutside_of_corr_of_tame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PetEqZeroOfNeOfHasCentChar
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CuspOrth

theorem pet_eq_zero_of_ne_of_hasCentChar : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] (π π' : CuspSub E a) (ω : HChar E), ω.IsUnitary →
    π.HasCentChar ω → π'.HasCentChar ω → CG.mk π ≠ CG.mk π' →
    ∀ φ ∈ π.V, ∀ φ' ∈ π'.V, pet (latticeGL E a) μ φ.1 φ'.1 = 0 := by
  intro E _ _ _ a μ _ π π' ω hω hπ hπ' hne
  exact pet_eq_zero_of_mk_ne μ hω (CuspSub.hasCentral_iff.2 hπ) (CuspSub.hasCentral_iff.2 hπ') hne

end GlobalTheory.CuspOrth
end

