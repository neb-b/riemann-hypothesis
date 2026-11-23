module

public import Formalism.AdmissibleDesigns.H1MapMemLcH1
public import Formalism.AdmissibleDesigns.CocZeroOfUnr
public import Formalism.AdmissibleDesigns.H1MapMemLocallyConstant
public import Formalism.AdmissibleDesigns.Bundle0007
public import Formalism.AdmissibleDesigns.Bundle0003
public import Formalism.AdmissibleDesigns.HigherColumnInvariantsBound

@[expose] public section

-- bundled from Formalism.AdmissibleDesigns.CoefChangeRec
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.ShaT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.MainNotions.N.K.QS Formalism.RepresentationBoundsCohomology.FIN
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem coefChange_rec : CoefChange (D.nd.l i) (D.nd.O i) :=
  CoefT.coefChange _ _

theorem tieSel2_full [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
    {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))} {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))}
    {π : D.nd.X i} {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1)) (hc : 2 ≤ (c : ℕ)) :
    TieSel2 i (Mc i Dd c) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) (qsN i dc)
      (Fall i dc Dd F0 c) (Io i) (IS i) (c : ℕ) := by
  exact tieSel2_rec (i := i) (dc := dc) (Dd := Dd) (hD := hD) (hN := hN) (F0 := F0) (c := c) (hc := hc)
    (hC := coefChange_rec i) (hZ := fun e _ => zlSha i dc e)

end Formalism.MainNotions.N.K.ShaT

end
end

-- bundled from Formalism.AdmissibleDesigns.ContWRec
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem contW_rec (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (l : K.Col i dc) :
    KDim.ContW (i := i) (dc := dc) (ρ := ρ) (π := π) l :=
  contW_of i dc ρ π (K.Norm.rhoCont_of i r ρ π hd hc) l

end Formalism.MainNotions.N.KOrb

end
end

-- bundled from Formalism.AdmissibleDesigns.KernelLengthHigherColumns
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.H0

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.NG Formalism.BasicNotions Formalism.RepresentationBoundsCohomology.FIN
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Gen
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def kogTo (k : ℕ) : KOG O k →ₗ[O] (Fin k → KO O) :=
  Submodule.liftQ _ (LinearMap.compLeft (1 : Submodule O (FractionRing O)).mkQ (Fin k)) (by
    rintro _ ⟨u, rfl⟩
    rw [LinearMap.mem_ker]
    funext a
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_one.2 ⟨u a, rfl⟩))

theorem kogTo_mk (k : ℕ) (v : Fin k → FractionRing O) :
    kogTo k (Submodule.Quotient.mk v : KOG O k) = fun a => (Submodule.Quotient.mk (v a) : KO O) := rfl

theorem kogTo_bijective (k : ℕ) : Function.Bijective (kogTo (O := O) k) := by
  constructor
  · intro x y hxy
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [kogTo_mk, kogTo_mk] at hxy
    refine (Submodule.Quotient.eq _).2 ?_
    have h : ∀ a, v a - w a ∈ (1 : Submodule O (FractionRing O)) := fun a =>
      (Submodule.Quotient.eq _).1 (congrFun hxy a)
    choose u hu using fun a => Submodule.mem_one.1 (h a)
    exact ⟨u, funext fun a => hu a⟩
  · intro f
    choose c hc using fun a => Submodule.Quotient.mk_surjective (1 : Submodule O (FractionRing O)) (f a)
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    rw [kogTo_mk]
    funext a
    exact hc a

def kogEq (k : ℕ) : KOG O k ≃ₗ[O] (Fin k → KO O) := LinearEquiv.ofBijective (kogTo k) (kogTo_bijective k)

theorem kogEq_apply (k : ℕ) (x : KOG O k) : kogEq k x = kogTo k x := rfl

theorem kogEq_WKG {Γ : Type} [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) O) (g : Γ) (x : KOG O k) (a : Fin k) :
    kogEq k (WKG M g x) a = ∑ b, M g a b • kogEq k x b := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show WKG M g (Submodule.Quotient.mk v : KOG O k) = Submodule.Quotient.mk _ from rfl]
  simp only [kogEq_apply, kogTo_mk]
  rw [← Submodule.mkQ_apply]
  trans Submodule.mkQ (1 : Submodule O (FractionRing O)) (∑ b, M g a b • v b)
  · congr 1
    simp only [LinearMap.restrictScalars_apply]
    unfold matRep mapM
    simp [Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
  · rw [map_sum]
    simp only [map_smul, Submodule.mkQ_apply]

end Gen

structure FinCore : Prop where
  w : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.admG2 i r ρ π →
    ∀ w ∈ placesOver D.host.E (D.nd.l i),
      Module.length (D.nd.O i) ↥(Representation.invariants ((Br.WKO i ρ π).comp (decS D.nd w))) < ⊤
  e : ∀ (D : D7) (i : D.nd.Loc), ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ e : ℕ, 0 < e →
    Module.length (D.nd.O i) ↥(Representation.invariants ((Formalism.MainNotions.N.Glob.KOtw D.nd i (e : ℤ)).comp (decS D.nd w))) < ⊤

def e0 {D : D7} : Fin D.R.r ≃ {a // RepresentationBoundsCohomology.blk D.R a = 0} := RepresentationBoundsCohomology.blockZeroEquiv D.R.r D.R.t

theorem length_ker_le {O G M M' : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (S : Submodule O M) (ρ' : Representation O G M') (f : M →ₗ[O] M') (hf : Function.Injective f)
    (h : ∀ m ∈ S, ∀ g, ρ' g (f m) = f m) :
    Module.length O ↥S ≤ Module.length O ↥(Representation.invariants ρ') := by
  let φ : S →ₗ[O] ↥(Representation.invariants ρ') :=
    LinearMap.codRestrict (Representation.invariants ρ') (f ∘ₗ S.subtype)
      (fun m => (Representation.mem_invariants ρ' _).2 fun g => h m m.2 g)
  exact Module.length_le_of_injective φ
    (fun a b hab => Subtype.ext (hf (congrArg Subtype.val hab)))

section Rec

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

def toKOG : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0 →ₗ[D.nd.O i] KOG (D.nd.O i) D.R.r where
  toFun m := (kogEq D.R.r).symm (fun a => m (e0 a))
  map_add' a b := by rw [← map_add (f := _)]; rfl
  map_smul' c a := by rw [RingHom.id_apply, ← map_smul]; rfl

theorem toKOG_injective : Function.Injective (toKOG i Dd) := by
  intro m m' hm
  have h' : (fun a => m (e0 a)) = (fun a => m' (e0 a)) := (kogEq D.R.r).symm.injective hm
  funext j
  obtain ⟨a, rfl⟩ := (e0 (D := D)).surjective j
  exact congrFun h' a

variable {i r ρ π g0 eB e₁ s Dd} in
theorem unipotent_block_zero_entry (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (g : GE D.nd) (a b : Fin D.R.r) :
    Dd.ρk 0 (uElt Dd.r Dd.χ g) (e0 a) (e0 b) = WpO D.nd i ρ π g a b := by
  have hE := ShaT.evS_of hD
  rw [← hE.ρk_eval]
  show Dd.ρπ (uElt Dd.r Dd.χ g) (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b) = _
  apply IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))
  have h := congrFun (congrFun (hE.ρπ_eval (uElt Dd.r Dd.χ g)) (Fin.castAdd D.R.t a)) (Fin.castAdd D.R.t b)
  refine Eq.trans h ?_
  rw [uElt, hE.smul_eval, hE.r_eval, hE.pπ, ← map_inv, hE.chi_eval, map_inv]
  show algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) _ *
    algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (rO D.nd i r π g (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b)) = _
  rw [hN.2.2 g a b, ← map_mul]
  rfl

variable [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

variable {i r ρ π g0 eB e₁ s Dd} in
theorem toKOG_equiv (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (g : GE D.nd) (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) :
    toKOG i Dd (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ g m) = Br.WKO i ρ π g (toKOG i Dd m) := by
  apply (kogEq D.R.r).injective
  funext a
  simp only [toKOG, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]
  unfold Br.WKO
  rw [kogEq_WKG]
  simp only [LinearEquiv.apply_symm_apply, ← unipotent_block_zero_entry hD hN]
  have hs := Equiv.sum_comp (e0 (D := D)) (fun j => Dd.ρk 0 (uElt Dd.r Dd.χ g) (e0 a) j • m j)
  rw [hs]
  rfl

def h0d (w : ℕ) : ℕ∞ :=
  Module.length (D.nd.O i) (LinearMap.ker (colDO (O := D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ
    ((decs D.host.E (Aw i dc)) w)))

theorem invariants_display_match (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) : LeTwistInvariantsAtColumns i ρ π dc (h0d i dc Dd) := by
  unfold LeTwistInvariantsAtColumns
  intro n hn
  unfold twistInvariantsLength h0d
  refine length_ker_le _ _ (toKOG i Dd) (toKOG_injective i Dd) ?_
  intro m hm g
  rw [MonoidHom.comp_apply, ← toKOG_equiv hD hN]
  congr 1
  rw [LinearMap.mem_ker] at hm
  unfold colDO at hm
  simp only [LinearMap.coe_mk, AddHom.coe_mk] at hm
  exact sub_eq_zero.1 (congrFun hm g)

variable {i r ρ π g0 eB e₁ s Dd} in
theorem kernel_length_higher_columns [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (c : Fin (D.R.t + 1)) (hc : 2 ≤ (c : ℕ)) :
    ∀ w ∈ Finset.univ.image (colIdx i dc), Module.length (D.nd.O i)
      (LinearMap.ker (colDO (O := D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) Dd.r Dd.χ ((decs D.host.E (Aw i dc)) w))) ≤
      invariantsLengthSup i dc := by
  intro w hw
  rw [cols_eq] at hw
  have hk : (c : ℕ) - 1 ∈ Finset.Ioo 0 D.R.t := Finset.mem_Ioo.2 ⟨by omega, by have := c.2; omega⟩
  refine le_H0N i dc hw hk ?_
  obtain ⟨φ, hφ⟩ := ShaT.blkTw_of_def hD hN c (by omega)
  let κ : KO (D.nd.O i) ≃ₗ[D.nd.O i] KmodO (D.nd.O i) := Submodule.quotEquivOfEq _ _ Submodule.one_eq_range
  refine length_ker_le _ _ ((φ.trans κ).toLinearMap) (φ.trans κ).injective (fun m hm g => ?_)
  have h1 : uElt Dd.r Dd.χ g.1 • m - m = 0 := congrFun (LinearMap.mem_ker.1 hm) g
  have h3 : uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) Dd.r Dd.χ g.1 m = m := sub_eq_zero.1 h1
  have h2 := hφ g.1 m
  rw [h3] at h2
  show ((((Formalism.MainNotions.N.Glob.epsO D.nd i) ^ (-((((c : ℕ) - 1 : ℕ)) : ℤ))) g.1 : (D.nd.O i)ˣ) : D.nd.O i) • κ (φ m) = κ (φ m)
  rw [← map_smul]
  congr 1
  refine Eq.trans ?_ h2.symm
  show _ = ((((Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom).comp
    (ShaT.cycE i ^ (-((((c : ℕ) - 1 : ℕ)) : ℤ)))) g.1 : (D.nd.O i)ˣ) : D.nd.O i) • φ m
  congr 2
  simp only [MonoidHom.comp_apply, MonoidHom.zpow_apply, map_zpow]
  rfl

end Rec

theorem theorem_of_display_and_g2 [hFin : Fact FinCore] {D : D7} (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (hD : D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → Br.sFin D.loc D.nbr i ρ π →
      (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
      SelmerLengthInequality i ρ π dc lenRow e' cB)
    (g2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (g5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) : TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB :=
  theorem_of_display i ρ π dc lenRow e' cB hD
    (fun w hw => hFin.out.w D i r ρ π g2 w ((dc.cover w).1 (Or.inr hw)))
    (fun w hw e he => hFin.out.e D i w ((dc.cover w).1 (Or.inr hw)) e (Finset.mem_Ioo.1 he).1) g5x

end Formalism.MainNotions.N.K.H0

end
end

-- bundled from Formalism.AdmissibleDesigns.TrivialBoundTargetOfDict
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Len

variable {R S : Type} [CommRing R] [CommRing S] (σ : R ≃+* S)

theorem length_le_semi {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M →+ N) (hf : Function.Injective f) (hs : ∀ (a : R) (m : M), f (a • m) = σ a • f m) :
    Module.length R M ≤ Module.length S N := by
  classical
  rw [Module.length_eq_height, Module.length_eq_height]
  let F : Submodule R M → Submodule S N := fun p =>
    { carrier := f '' p
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, p.add_mem hx hy, map_add f x y⟩
      zero_mem' := ⟨0, p.zero_mem, map_zero f⟩
      smul_mem' := by
        rintro s _ ⟨x, hx, rfl⟩
        refine ⟨σ.symm s • x, p.smul_mem _ hx, ?_⟩
        rw [hs, RingEquiv.apply_symm_apply] }
  have hF : StrictMono F := by
    intro p q hpq
    rw [SetLike.lt_iff_le_and_exists] at hpq ⊢
    obtain ⟨hle, x, hxq, hxp⟩ := hpq
    refine ⟨?_, f x, ⟨x, hxq, rfl⟩, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hle hy, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact hxp (hf hyx ▸ hy)
  exact (Order.height_le_height_apply_of_strictMono F hF ⊤).trans (Order.height_mono le_top)

theorem length_quot_eq (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = Module.length S (S ⧸ Ideal.span {σ a}) := by
  classical
  have hJ : Ideal.span {σ a} = (Ideal.span {a}).map (σ : R →+* S) := by
    simp [Ideal.map_span]
  let e := Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {σ a}) σ hJ
  have he : ∀ (r : R) (x : R ⧸ Ideal.span {a}), e (r • x) = σ r • e x := by
    intro r x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [e, Ideal.quotientEquiv_apply, Algebra.smul_def, Ideal.quotientMap_mk, Ideal.Quotient.algebraMap_eq]
  refine le_antisymm (length_le_semi σ e.toAddEquiv.toAddMonoidHom e.injective he) ?_
  refine length_le_semi σ.symm e.symm.toAddEquiv.toAddMonoidHom e.symm.injective ?_
  intro s y
  apply e.injective
  show e (e.symm (s • y)) = e (σ.symm s • e.symm y)
  rw [he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

end Len

section QRec

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL] {e : ℕ}

abbrev QrecS (Ce : TwLat PD LL O e) (cB : ℕ) : Submodule O (G → Ce.V ⧸ Ce.L.T) :=
  divisibleCocycles Ce.L ⊓ (HfD PD Ce.L).comap (((PD.p : O) ^ cB) • LinearMap.id)

abbrev Qrec (Ce : TwLat PD LL O e) (cB : ℕ) : Type :=
  ↥(QrecS PD Ce cB) ⧸ (divisibleCocycles Ce.L ⊓ HfD PD Ce.L).comap (QrecS PD Ce cB).subtype

def LenMap {O' : Type} [CommRing O'] (σ : O' ≃+* O) (X : Type) [AddCommGroup X] [Module O' X]
    (Ce : TwLat PD LL O e) (cB : ℕ) : Prop :=
  ∃ f : X →+ Qrec PD Ce cB, Function.Injective f ∧ ∀ (a : O') (x : X), f (a • x) = σ a • f x

theorem len_gen {t cB : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (het : e < t) (Ce : TwLat PD LL O e)
    {O' : Type} [CommRing O'] (σ : O' ≃+* O) {X : Type} [AddCommGroup X] [Module O' X]
    (h : LenMap PD σ X Ce cB) :
    Module.length O' X ≤ ((finrank Qp K : ℕ∞) + 1) * (cB : ℕ∞) * lenOl PD (O := O) := by
  obtain ⟨f, hf, hs⟩ := h
  refine (length_le_semi σ f hf hs).trans ?_
  cases Ce
  exact (hTB.2 e het _ _ _ (by assumption) (by assumption)).2.2

end QRec

section RecLen

open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def TBDict2 (cB : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) →
      ∃ (Y : YtLat (G := Br.G D.nbr i w hw) (Qp := ℚ_[D.nd.l i]) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL))
        (Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w))
          (eW i dc hw) ((c : ℕ) - 1)),
        YtCrys (PD := Br.PD D.loc D.nbr i w hw) Y (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) ∧
        PsiExt (selfO i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) Y Cd ∧
        YLoc (O := D.nd.O i) (Mc i Dd c) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) ∧
        LenMap (Br.PD D.loc D.nbr i w hw) (selfO i hw) (Qcore i dc Dd c (idx i dc w) cB) Cd.Ce cB


set_option maxHeartbeats 800000 in
private theorem lenMap_Qcore (cB : ℕ) (hd : TBDict2 i dc r π Dd cB) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hwrow : w ∈ dc.row)
    (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ)) :
    ∃ Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w))
          (eW i dc hw) ((c : ℕ) - 1),
      LenMap (Br.PD D.loc D.nbr i w hw) (selfO i hw) (Qcore i dc Dd c (idx i dc w) cB) Cd.Ce cB :=
  (hd w hw hwrow c hc).elim fun _ h => h.elim fun Cd h' => ⟨Cd, h'.2.2.2⟩

theorem tbDict_of (cB : ℕ) (h : TBDict2 i dc r π Dd cB) : TBDict i dc r π Dd := by
  unfold TBDict2 at h
  unfold TBDict
  intro w hw hrow c hc
  obtain ⟨Y, Cd, h1, h2, h3, -⟩ := h w hw hrow c hc
  exact ⟨Y, Cd, h1, h2, h3⟩


set_option maxHeartbeats 1000000 in
theorem tbLen_w (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i)
    (hd : TBDict2 i dc r π Dd cB) {w : HeightOneSpectrum (𝓞 D.host.E)} (hwrow : w ∈ dc.row)
    (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ)) : TBLenAt i dc Dd cB (idx i dc w) c := by
  have hw : w ∈ placesOver D.host.E (D.nd.l i) := (dc.cover w).1 (Or.inl hwrow)
  have hpl : w ∈ plSet i dc := by simp [plSet, hwrow]
  unfold TrivialBoundAtRows at hTB
  unfold TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility at hTie
  obtain ⟨Cd, hL⟩ := lenMap_Qcore (hd := hd) (hw := hw) (hwrow := hwrow) (c := c) (hc := hc)
  have het : (c : ℕ) - 1 < D.R.t := by have := c.isLt; omega
  have hdeg := (hTie w hw).2.2
  unfold Br.DegW at hdeg

  have aux : ∀ {R' S' : Type} [CommRing R'] [CommRing S'] (σ' : R' ≃+* S') (n : ℕ),
      Module.length R' (R' ⧸ Ideal.span {(n : R')}) = Module.length S' (S' ⧸ Ideal.span {(n : S')}) := by
    intro R' S' _ _ σ' n
    rw [length_quot_eq σ', map_natCast]
  unfold TBLenAt
  refine le_trans (len_gen (Br.PD D.loc D.nbr i w hw) (hTB w hw hwrow) het Cd.Ce (selfO i hw) hL) (le_of_eq ?_)
  rw [plOf_idx (h := hpl), ← hdeg]
  unfold lenOl
  rw [Br.PD_p, ← aux (selfO i hw) (D.nd.l i)]
  ring

theorem tbLen_of (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i)
    (hd : TBDict2 i dc r π Dd cB) : TBLen i dc Dd cB := by
  unfold TBLen
  intro n hn c hc
  unfold rowsN at hn
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hn
  exact tbLen_w (hTB := hTB) (hTie := hTie) (hd := hd) (hwrow := hw) (c := c) (hc := hc)

theorem trivial_bound_target_of_dict (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i)
    (hd : TBDict2 i dc r π Dd cB) : TBTarget i dc Dd cB :=
  tbTarget_of (hTB := hTB) (hd := tbDict_of (h := hd)) (hlen := tbLen_of (hTB := hTB) (hTie := hTie) (hd := hd))

end RecLen

end Formalism.MainNotions.N.K.TB

end
end

