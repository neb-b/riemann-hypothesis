module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0019
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR.Mult
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def ev (M : DSModel V S) (v₀ : M.Vec) : MMap M →ₗ[ℂ] (GA D V → ℂ) where
  toFun T := T v₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ev_apply (M : DSModel V S) (v₀ : M.Vec) (T : MMap M) : ev M v₀ T = T v₀ := rfl


end Formalism.IndefR.AutomorphicEvaluation

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CoreTExist
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.CoreT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj
  Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Half

variable (P : Formalism.L2.Host.PiBar D.host)


variable (hF : OFull D) (hz : OZeta D) (hN : N1ab)

end Half

section Chr

theorem mem_of_latHat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Λ) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) {x : Fin n → E}
    (h : (fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E))) : x ∈ Λ := by
  have key : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)),
      (fun i => Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (y i)) ∈
        Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have hs : (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E := Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩)
      have hv : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈
          Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ := Submodule.subset_span ⟨x, hx, rfl⟩
      convert Submodule.smul_mem _ (⟨(1 : E) ⊗ₜ[F] a, hs⟩ : Formalism.L2.Herm.intAf F E) hv using 1
      funext i
      show Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (a ⊗ₜ[F] x i) =
        ((1 : E) ⊗ₜ[F] a) * (x i ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rfl
    | zero =>
      convert Submodule.zero_mem (Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ) using 1
      funext i
      exact map_zero _
    | add y z _ _ hy hz =>
      convert add_mem hy hz using 1
      funext i
      exact map_add _ _ _
    | neg y _ hy =>
      convert neg_mem hy using 1
      funext i
      exact map_neg _ _
  have hg : x ∈ Formalism.UG.CS.globLat (F := F) 1 Λ := by
    show ((1⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
      (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈
        Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
    exact key _ h
  rwa [Formalism.UG.P.global_lattice_one_holds F E (Fin n) Λ hfin hsp] at hg

end Chr

section Unif

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}



variable {U : Unf Xo c σ r} {V : HSp D} {dict : GA D V → Σ k, Frame (U.X k).Ψ r} {mu : GA D V → ℂ}

end Unif

section Core

variable (Q : Par D)

variable {Q}

end Core

section Rec

variable (Q : Par D)



variable {Q}

end Rec

section Pg

end Pg

section Rows

section Gen

variable {F E R : Type} [Field F] [CharZero F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] (s : E →ₐ[F] E)
  (hs : ∀ e, ∃ f : F, algebraMap F E f = e + s e)

include hs

end Gen

section H90

end H90

end Rows

section Cover

open CategoryTheory

attribute [local instance] Over.cartesianMonoidalCategory

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

variable {Xo c}

end Cover

section IdMap

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

section Cech

variable {X Y : Scheme.{0}}

variable (L : LB X)

variable {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)


end Cech

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}


end IdMap

section Trans

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

include hle

end Trans

section Lat

variable {n : ℕ}

end Lat

section OM

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}



variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (v₀ : (R.MW i (sg0 D A)).Vec)
  (c' : Coeff T.Q.l) (jL : D.what₂.LL →+* c'.F) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)

variable {T R i v₀ c' jL lev}

end OM

end Formalism.IndefR.CoreT
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.PrimitivePackageFullHecke
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section End3

open Formalism.IndefR.Cx Formalism.L2.Geo Formalism.MainNotions

variable [_root_.NumberField.IsTotallyComplex D.what₂.LL] {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def PassIn3 (R : RealDat3 D A3 Ks) (F : Face3 D A3) (C CH : ℝ) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (Ws : S → Type) (_ : ∀ s, AddCommGroup (Ws s)) (_ : ∀ s, Module D.what₂.LL (Ws s))
    (_ : ∀ s, FiniteDimensional D.what₂.LL (Ws s)) (τ : ∀ s, Representation D.what₂.LL G (Ws s)) (nbar : ℝ),
    CxPassIn3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F) C CH S Ws τ nbar

def primitivePackageFullHecke {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (H : HkDat3 A3) (C CH : ℝ) (hC : R.WeakCharacterisation F)
    (hP : CovolumeOntoIsometryConditions R F sEE H C CH) (hI : PassIn3 R F C CH) :
    IndefPkgR A3.fam3.amb3 (faceOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) (R.convOf F H) C CH :=
  letI := hI.choose_spec.choose
  letI := hI.choose_spec.choose_spec.choose_spec.choose
  letI := hI.choose_spec.choose_spec.choose_spec.choose_spec.choose
  letI := hI.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  packageFullHecke (base_lifts_package_of_primitive_links hOk hsep hC hP) hI.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

def primRows3 {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F)
    (hP : PrimRows3 R F) : IndefRows (lv (F.fc (R.toCx3 F).zs) false) :=
  indefiniteDataAtBaseLevel (complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP)

theorem primRows3_data {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) {R : RealDat3 D A3 Ks} {F : Face3 D A3}
    (hC : R.WeakCharacterisation F) (hP : PrimRows3 R F) : (primRows3 hOk hsep R F hC hP).toIndefData = (R.toCx3 F).data F.cr false := rfl

end End3

end Formalism.IndefR.Links

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.SpOfRwRange
section
open Module NumberField IsDedekindDomain
open scoped Matrix InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.BasicNotions Formalism.L2.Col Formalism.IndefR.Links

section Face

variable {Fl : Fields} {Pr : Primes Fl} {Rk : Ranks} (W : Wts Fl Pr.Word Rk) (Ch : Chars Fl Pr Rk.m)
  (sel : HeightOneSpectrum (𝓞 Fl.F) → HeightOneSpectrum (𝓞 Fl.E)) {Sg : Set ℕ}
  {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

end Face

section Sp

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

structure PerW (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word) where

  Dt : Set X.B.I.GA
  hD : IsReps X u Dt
  hin : InHH X u hK
  hlin : PuLinear X u hK Dt

  F : Formalism.L2.Forms.Forms0 D u

  Tr : Transport X u F
  hI : ColDictInto X Tr hK
  hB : ColDictBij X Tr hK

variable {X}

def PerW.op {hK : X.LevelSubgroupCharacter} {u : D.what₂.Word} (p : PerW X hK u) : (D.mem u).A.Mu0 →ₗ[ℂ] HHX X :=
  Formalism.L2.SG.PoincareInHH.PoincareSetting.Pu X u hK p.Dt p.hD p.hin p.hlin ∘ₗ (colDict X p.Tr hK p.hI p.hB).symm.toLinearMap

def ramCrd {u : D.what₂.Word} {n : ℕ} (bR : Fin n → (D.mem u).A.Mram) : (Fin n → ℂ) →ₗ[ℂ] (D.mem u).A.Mu0 :=
  Submodule.inclusion inf_le_left ∘ₗ Fintype.linearCombination ℂ bR

def cjVec (s : Bool) (n : ℕ) : (Fin n → ℂ) →ₛₗ[cj s] (Fin n → ℂ) where
  toFun φ i := cj s (φ i)
  map_add' φ ψ := by funext i; simp
  map_smul' a φ := by funext i; simp

def perTw (s : Bool) {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] HHX X) : (Fin n → ℂ) →ₗ[ℂ] Tw s (HHX X) :=
  Tw.semi (σ := cj s) (σ' := RingHom.id ℂ) s (fun a => (cj_cj s a).symm) (f.comp (cjVec s n))

def spOf (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (Dc : DefCols Df) (hK : X.LevelSubgroupCharacter) (G : GoodOp X)
    (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW X hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) : SPer Dc where
  HH := Tw s (HHX X)
  nHH := inferInstance
  iHH := inferInstance
  Pu x := perTw s ((pw x).op ∘ₗ ramCrd (bR x))
  Rw := Tw.sub s ((goodSub X G).comap (HHX X).subtype)

section Facts

variable (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (Dc : DefCols Df) (hK : X.LevelSubgroupCharacter) (G : GoodOp X)
  (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW X hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram)

theorem spOf_Pu (x : Dc.Mem) (φ : Fin (Dc.a x) → ℂ) :
    Tw.out (s := s) ((spOf s Dc hK G wdD pw bR).Pu x φ) = (pw x).op (ramCrd (bR x) (cjVec s _ φ)) := rfl

end Facts

end Sp

section Seam


end Seam

section FaceSp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}

end FaceSp

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.ThPinsEx
section
noncomputable section

namespace Formalism.IndefR.FWT

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct nonZeroDivisors

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Gen

section Map

open MvPolynomial

end Map

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem Q_base_empty (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
  have h := (hL.Q_ram A.μ0 PP).2 (Or.inl hPP)
  rw [hL.xi_base] at h
  exact h fun x _ => rfl

section Phi

variable (R : RealDat D A Ks) (i : Fin D.R.m) {K' : Type} [Field K'] (σ' : K' →+* ℂ) (t : T0)
  {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
  (N : Submodule (𝓞 D.host.E) La)

end Phi

section Reps

variable (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)

end Reps

section Place

variable (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0) {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i))
  {K' : Type} [Field K'] {jL : D.what₂.LL →+* K'} {σ' : K' →+* ℂ}

theorem levFn_flag1_mem {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (S : Subfield ℂ)
    (hcg : ∀ c, ∀ PP ∈ L.Pg, ∀ u, ((L.cg c PP u : ℂˣ) : ℂ) ∈ S) (hxq : ∀ PP ∈ L.Q, ∀ u, ((L.xq PP u : ℂˣ) : ℂ) ∈ S)
    (x : GL (Fin n) (Lev.EAf D)) :
    ((Formalism.L2.DIV.levFn β (Lev.flag1L L) x : ℂˣ) : ℂ) ∈ S := by
  unfold Formalism.L2.DIV.levFn
  simp only [Units.val_mul, Units.coe_prod]
  refine S.mul_mem (S.mul_mem ?_ (S.prod_mem fun PP hPP => S.prod_mem fun c _ => hcg _ _ hPP _))
    (S.prod_mem fun PP hPP => hxq _ hPP _)
  unfold Formalism.L2.DIV.ext1
  split_ifs
  · have e : (Lev.flag1L L).P.chi = 1 := rfl
    rw [e, MonoidHom.one_apply, Units.val_one]
    exact S.one_mem
  · simp only [Units.val_one]
    exact S.one_mem


set_option maxHeartbeats 2000000 in
theorem hχ_of (hchi : ∀ PP ∈ R.Pg, ∀ u, ∃ a, ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ) = D.what₂.embLL a)
    (hxi : ∀ PP ∈ R.Q t, ∀ u, ∃ a, ((R.xiR t PP u : ℂˣ) : ℂ) = D.what₂.embLL a) :
    ∀ k, ∃ a, (((levEnvOf (Vc D i) (R.βV i) (R.toLevCh.datVt i t) R.pl (A.ok t)).lev.χ k : ℂˣ) : ℂ) = D.what₂.embLL a := by
  intro k
  have hcg : ∀ c, ∀ PP ∈ (R.toLevCh.datVt i t).Pg, ∀ u,
      (((R.toLevCh.datVt i t).cg c PP u : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
    intro c PP hPP u
    have e : (R.toLevCh.datVt i t).cg c PP u = (R.chi ((i : ℕ) + 1) PP u)⁻¹ := by
      simp [LevCh.datVt, Lev.datY]
    rw [e, Units.val_inv_eq_inv_val]
    obtain ⟨a, ha⟩ := hchi PP hPP u
    exact Subfield.inv_mem _ ⟨a, ha.symm⟩
  have hxq : ∀ PP ∈ (R.toLevCh.datVt i t).Q, ∀ u,
      (((R.toLevCh.datVt i t).xq PP u : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
    intro PP hPP u
    have e : (R.toLevCh.datVt i t).xq PP u = R.xiR t PP u := by
      simp [LevCh.datVt, Lev.datY]
    rw [e]
    obtain ⟨a, ha⟩ := hxi PP hPP u
    exact ⟨a, ha.symm⟩
  obtain ⟨a, ha⟩ := levFn_flag1_mem (R.βV i) (R.toLevCh.datVt i t) D.what₂.embLL.fieldRange hcg hxq _
  exact ⟨a, ha.symm⟩

end Place

section Assemble

end Assemble

end Formalism.IndefR.FWT

end
end

