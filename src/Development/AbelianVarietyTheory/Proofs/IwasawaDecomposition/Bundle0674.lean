module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0011
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftAdelicFormLevelTypeEqColumnLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0260

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonCoefficientMapLiftPresentation
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftPresStd

theorem vv_cast_equiv : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι]
    (emb : ι → E →+* K) {n n' : ℕ} (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n'),
    (∀ τ a, (lam τ).w a = (lam' τ).w (Fin.cast h a)) →
    ∃ e : VV K lam ≃ₗ[K] VV K lam',
      (∀ (g : GL (Fin n') E) v, e (rhoVr emb lam (LiftBrg.castGL h.symm g) v) = rhoVr emb lam' g (e v)) ∧
      (∀ (J : Matrix (Fin n) (Fin n) E) x y,
        pairVr emb lam' (J.reindex (finCongr h) (finCongr h)) (e x) (e y) = pairVr emb lam J x y) ∧
      (∀ N : Submodule (𝓞 E) (Fin n → E), (nabAtr emb lam N).map (e.toLinearMap.restrictScalars (𝓞 K)) =
        nabAtr emb lam' (N.map (LinearEquiv.funCongrLeft (𝓞 E) E (finCongr h).symm).toLinearMap)) ∧
      (∀ N : Submodule (𝓞 E) (Fin n → E), (delAtr emb lam N).map (e.toLinearMap.restrictScalars (𝓞 K)) =
        delAtr emb lam' (N.map (LinearEquiv.funCongrLeft (𝓞 E) E (finCongr h).symm).toLinearMap)) ∧
      (∀ i j, (bVV K lam').repr (e (bVV K lam i)) j ∈ Formalism.DivisionValues.cmMax K) ∧
      (∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (c0 : VV K lam' →ₛₗ[σ] W),
        LinearIndependent ℂ (fun i => c0 (bVV K lam' i)) → Submodule.span ℂ (Set.range fun i => c0 (bVV K lam' i)) = ⊤ →
        LinearIndependent ℂ (fun i => c0 (e (bVV K lam i))) ∧ Submodule.span ℂ (Set.range fun i => c0 (e (bVV K lam i))) = ⊤) := by
  intro E K _ _ _ _ _ ι _ emb n n' h lam lam' hl
  subst h
  have hlam : lam = lam' := by
    funext τ
    have h1 := hl τ
    rcases hw : lam τ with ⟨w, hw1⟩
    rcases hw' : lam' τ with ⟨w', hw1'⟩
    rw [hw, hw'] at h1
    have : w = w' := funext fun a => by simpa using h1 a
    subst this
    rfl
  subst hlam
  have hN : ∀ N : Submodule (𝓞 E) (Fin n → E),
      N.map (LinearEquiv.funCongrLeft (𝓞 E) E (finCongr (rfl : n = n)).symm).toLinearMap = N := by
    intro N
    ext x
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      convert hy using 1
      funext a
      rfl
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨LinearEquiv.refl K _, fun g v => ?_, fun J x y => ?_, fun N => ?_, fun N => ?_, fun i j => ?_, fun W _ _ σ c0 h1 h2 => ⟨h1, h2⟩⟩
  · have : LiftBrg.castGL (rfl : n = n).symm g = g := by ext a b; simp [LiftBrg.castGL]
    rw [this]; rfl
  · have : J.reindex (finCongr (rfl : n = n)) (finCongr (rfl : n = n)) = J := by ext a b; simp
    rw [this]; rfl
  · rw [hN]; exact Submodule.map_id _
  · rw [hN]; exact Submodule.map_id _
  · show (bVV K lam).repr (bVV K lam i) j ∈ Formalism.DivisionValues.cmMax K
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem ufGL_ratHom : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (γ : Formalism.L2.Col.URat hc n),
    Formalism.L2.Col.ufGL E n (Formalism.L2.Col.ratHom hc n γ) = (γ : GL (Fin n) E) := by
  intro F E _ _ _ _ _ _ hc n γ
  apply Units.ext
  ext a b
  simp [Formalism.L2.Col.ufGL, Formalism.L2.Col.toGLm, Formalism.L2.Col.ratHom, Formalism.UG.glEquiv, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv]

theorem formRho_colGl {X : Formalism.L2.Col.Fields} {n : ℕ} [NeZero n] {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (hc : Formalism.BasicNotions.CMData X.F X.E)
    (C : Formalism.L2.Col.CoefPk X n (Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG))) (Λ : Formalism.L2.Col.LevFam X.E X.K n SG)
    (γ : Formalism.L2.Col.URat hc n) (k : Bridge.colJ hc n ∅ SG Λ.grp) (v : C.V) :
    (Formalism.L2.Col.formGSD C Λ).ρ (Bridge.colGl (Formalism.L2.Col.rf_onDeco C Λ) (γ, k)) v =
      ((Λ.chr (Formalism.L2.Col.redH hc n ∅ SG Λ.grp ((Bridge.colJEquiv hc n ∅ SG Λ.grp).symm k)) : X.Kˣ) : X.K) •
        C.rho (Formalism.L2.Col.ratHom hc n γ) v := rfl

theorem castGL_symm_castGL {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (g : GL (Fin m) R) :
    LiftBrg.castGL h.symm (LiftBrg.castGL h g) = g := by
  subst h
  ext a b
  simp [LiftBrg.castGL]

theorem exists_oneCoef_presStd : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m)
    (c0L : VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W),
    (cV i).Is → Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef c0L (rhoVr (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0L x) (c0L y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _
      (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) →
    L.βV i = 1 → (Vc X.toD7 i).gram = 1 →
    ∃ c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W, (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v)) ∧
      ∀ t : TupU I U, ∃ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t 1 1 P ∧
        (∀ v, P.coef v = c v) ∧ Bridge.CoefTie (X.toD7.sp.V ((i : ℕ) + 1)) (cV i).coef P (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) c0L
        (pairVr (labLL X.toD7) _
          (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(X.toD7.sp.V ((i : ℕ) + 1)).gram else (X.toD7.sp.V ((i : ℕ) + 1)).gram))
        (nabAtr (labLL X.toD7) _) (delAtr (labLL X.toD7) _) := by
  intro X px I hX U Xg tr L eG0 hI hV hL hG cV i c0L hcV hmap hin hβ hgram
  obtain ⟨e0, he_rho, he_pair, he_nab, he_del, he_rat, he_li⟩ :=
    vv_cast_equiv X.B.fields.emb (LiftBrg.rkEq X i) (X.B.wts.lamV ((i : ℕ) + 1))
      (fun τ => Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) (GlobalTheory.T.baseWeight_eq_forcedLiftWeight X i)
  let c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W :=
    { toFun := fun v => c0L (e0 v)
      map_add' := fun v w => by show c0L (e0 (v + w)) = c0L (e0 v) + c0L (e0 w); rw [map_add (f := _)]; exact c0L.map_add _ _
      map_smul' := fun a v => by show c0L (e0 (a • v)) = _; rw [LinearEquiv.map_smul]; exact c0L.map_smulₛₗ a (e0 v) }
  have hc : ∀ v, c v = c0L (e0 v) := fun v => rfl
  have hint : ∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v) := by
    intro γ γE h v
    exact (congrArg c0L (he_rho γE v)).trans (hmap.1 γ γE h (e0 v))
  refine ⟨c, hint, fun t => ?_⟩
  obtain ⟨eG, eΓ, hchar, hι, hrat⟩ := _root_.GlobalTheory.Mem.R3.LiftBrg.StdGroups.stdGroups_equiv X i hgram
  obtain ⟨hJ, hχ⟩ := _root_.GlobalTheory.Mem.LevPres.lev_type_eq X px I U L hI hV hL i t eG hchar

  letI : Algebra X.toD7.host.F X.B.fields.E := inferInstanceAs (Algebra X.toD7.host.F X.toD7.host.E)
  have hneg : X.toD7.sp.Vneg ((i : ℕ) + 1) = false := X.B.V_pos _ (by omega) i.2
  have hgr : (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) =
      (1 : Matrix (Fin X.B.R.nV) (Fin X.B.R.nV) X.toD7.host.E).reindex (finCongr (LiftBrg.rkEq X i)) (finCongr (LiftBrg.rkEq X i)) := by
    rw [hneg, if_neg (by simp), hgram]
    ext a b
    simp [Matrix.one_apply]
  have hSG : Formalism.L2.Col.DecoPtSurj X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) :=
    Formalism.L2.Col.decoPtSurj_of _ _ _ _ (Formalism.L2.Col.unimodGenus_holds _ _) Formalism.L2.DIV.reduction_surjective_bis
      (by classical convert _root_.GlobalTheory.Mem.R3.LiftBrg.isSplitSet_sgL X px I U L hI hL t using 1; exact Finset.empty_union _) (Finset.disjoint_empty_left _)
  let o := Formalism.L2.Col.rf_onDeco (X := X.B.fields) (n := X.B.R.nV) (ST := ∅) (SG := LiftBrg.sgL X I U t)
    (Formalism.L2.Col.mtVal (Pr := X.B.primes px) X.B.wts ((i : ℕ) + 1) _) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv
  have hmem : ∀ k : Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
      (eG.toMonoidHom.comp (Subgroup.subtype _)) k ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J := fun k => by
    rw [hJ]; exact Subgroup.mem_map_of_mem _ k.2
  let χc := (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ.comp ((eG.toMonoidHom.comp (Subgroup.subtype _)).codRestrict _ hmem)
  have hχc : ∀ k, ((χc k)⁻¹ : ℂˣ) = Units.map X.toD7.what₂.embLL.toMonoidHom ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr
      (Formalism.L2.Col.redH X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _
        ((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _).symm k))) := fun k => (hχ k (hmem k)).1
  have hK1 : ∀ k : Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
      (k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) ∈ Bridge.principalCongruenceSubgroup X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) → χc k = 1 :=
    fun k hk => (hχ k (hmem k)).2 hk
  have hli := he_li (cV i).W X.toD7.what₂.embLL c0L hmap.2.1 hmap.2.2
  have hpair : ∀ x x', inner ℂ (c x) (c x') = X.toD7.what₂.embLL ((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).pair x x') := by
    intro x x'
    refine (hin (e0 x) (e0 x')).trans ?_
    congr 1
    rw [hgr]
    exact he_pair 1 x x'
  have hgl : ∀ (γ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV) k (v : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V),
      c ((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).ρ (Bridge.colGl o (γ, k)) v) =
        ((χc k)⁻¹ : ℂˣ) • ((cV i).coef.ρ.comp eΓ.toMonoidHom) γ (c v) := by
    intro γ k v
    rw [show (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).ρ (Bridge.colGl o (γ, k)) v = _ from
      formRho_colGl (X := X.B.fields) X.toD7.sp.cm _ _ γ k v]
    refine (c.map_smulₛₗ _ _).trans ?_
    have e3 : (Formalism.L2.Col.mtVal (Pr := X.B.primes px) X.B.wts ((i : ℕ) + 1) (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)).rho
        (Formalism.L2.Col.ratHom X.toD7.sp.cm X.B.R.nV γ) v =
        rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1))
          (LiftBrg.castGL (LiftBrg.rkEq X i).symm (LiftBrg.castGL (LiftBrg.rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E))) v := by
      show rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1))
        (Formalism.L2.Col.ufGL X.toD7.host.E X.B.R.nV (Formalism.L2.Col.ratHom X.toD7.sp.cm X.B.R.nV γ)) v = _
      rw [ufGL_ratHom]
      exact congrArg (fun g => rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) g v) (castGL_symm_castGL (LiftBrg.rkEq X i) _).symm
    have e2 := hint (eΓ γ) _ (hrat γ) v
    have e4 := (congrArg c e3).trans e2
    rw [hχc k, Units.smul_def]
    erw [e4]
    rfl

  let A := Bridge.colAdPts o hSG
  let P0 := Bridge.colClassPres (hc := X.toD7.sp.cm) o hSG (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1)) X.toD7.what₂.embLL
    ((cV i).coef.ρ.comp eΓ.toMonoidHom) χc c hli.1 hli.2 hpair hK1 hgl
  let P : LiftBrg.PresL X I hX U Xg tr L cV i t :=
    P0.transport eG eΓ hι (fun _ => rfl) hJ (fun k hk => rfl)
  refine ⟨P, ?_, fun v => rfl, e0, he_rat, fun x => rfl, ?_, ?_, ?_⟩

  · intro f g
    have h5 := _root_.GlobalTheory.Mem.TransportRead.transport_ext_eq (ι' := Bridge.ratF (Vc X.toD7 i)) (ρ' := (cV i).coef.ρ) (J' := (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J)
      (χ' := (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ) A (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1)) X.toD7.what₂.embLL
      ((cV i).coef.ρ.comp eΓ.toMonoidHom) χc c hli.1 hli.2 hpair hK1 hgl eG eΓ hι (fun _ => rfl) hJ (fun k hk => rfl) f g
    refine h5.trans ?_
    have hq : A.q (eG.symm g) = LiftBrg.ptL X I U i t 1 1 g := by
      show Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (QuotientGroup.mk (eG.symm g)) = _
      rw [Formalism.L2.Col.decoPt_mk]
      unfold LiftBrg.ptL
      congr 1
      have := hchar (eG.symm g)
      rw [MulEquiv.apply_symm_apply] at this
      rw [this]
      simp
    erw [hq]
    rfl
  · intro x x'
    rw [hgr]
    exact he_pair 1 x x'
  · intro cl
    have h6 := _root_.GlobalTheory.Mem.R3.LiftLatStd.hLat_eq_decoPt_N X i (L.ΛV i) (by rw [← hβ]; exact hL.is.βV i) (LiftBrg.sgL X I U t) eG hchar (A.y cl)
    have hy := A.q_y cl
    have hy' : Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (QuotientGroup.mk (A.y cl)) =
        (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).outSec.rep cl := hy
    refine Eq.trans ?_ (congrArg (nabAtr (labLL X.toD7) (fun τ => Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ)) h6).symm
    rw [hy']
    exact he_nab _
  · intro cl
    have h6 := _root_.GlobalTheory.Mem.R3.LiftLatStd.hLat_eq_decoPt_N X i (L.ΛV i) (by rw [← hβ]; exact hL.is.βV i) (LiftBrg.sgL X I U t) eG hchar (A.y cl)
    have hy := A.q_y cl
    have hy' : Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (QuotientGroup.mk (A.y cl)) =
        (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).outSec.rep cl := hy
    refine Eq.trans ?_ (congrArg (delAtr (labLL X.toD7) (fun τ => Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ)) h6).symm
    rw [hy']
    exact he_del _

end GlobalTheory.Mem.R3.LiftPresStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSmoothProjectiveRefinementPolyFan
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem GlobalTheory.PolFan.exists_smooth_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧ IsTwInv H φ' ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ' γ → ψ.LinearOn γ := by
  intro E _ _ _ H q ψ hD hψ hT
  obtain ⟨φ, lab, hφ, hφT, hlT, hSL, hsub⟩ := _root_.GlobalTheory.PolFan.exists_simpLab_refinement E H q ψ hD hψ hT
  obtain ⟨φ', h1, h2, h3, hsub'⟩ := _root_.GlobalTheory.PolFan.resolution E H q φ lab hD hφ hφT hlT hSL
  exact ⟨φ', h1, h2, h3, fun X _ _ _ _ hX m γ hγ => (hsub'.trans hsub).linearOn hX hγ.isCell⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataStateLocalisations
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.Fin3.MvLoc

section Three

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
variable {A : DIV.FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T₀ a.D.R.m} (R : Links.RealDat3 a.D A Ks)

def thrice : type_of% (real3 c R) := (by with_unfolding_all exact ((real3 (a := b) c (iK := alg b iK) (real3 b R)) :))

def thriceY : type_of% (letI := alg c iK; (real3 c R).ioY) := letI := alg c iK; (by with_unfolding_all exact ((thrice b c R).ioY :))

def thriceX : type_of% (letI := alg c iK; (real3 c R).ioX) := letI := alg c iK; (by with_unfolding_all exact ((thrice b c R).ioX :))

theorem thriceY_eq : letI := alg c iK; (real3 c R).ioY = thriceY b c R := by
  have h1 := real_ioY c R.toRealDat
  have h2 := real_ioY b R.toRealDat
  have h3 := real_ioY (a := b) c (iK := alg b iK) (real b R.toRealDat)
  have h4 : HEq _ (thriceY b c R) := HEq.trans (HEq.trans h1.symm h2) ((by with_unfolding_all exact (h3 :)))
  letI := alg c iK
  exact eq_of_heq ((by with_unfolding_all exact (h4 :)))

theorem thriceX_eq : letI := alg c iK; (real3 c R).ioX = thriceX b c R := by
  have h1 := real_ioX c R.toRealDat
  have h2 := real_ioX b R.toRealDat
  have h3 := real_ioX (a := b) c (iK := alg b iK) (real b R.toRealDat)
  have h4 : HEq _ (thriceX b c R) := HEq.trans (HEq.trans h1.symm h2) ((by with_unfolding_all exact (h3 :)))
  letI := alg c iK
  exact eq_of_heq ((by with_unfolding_all exact (h4 :)))

theorem thrice_eq : real3 c R = thrice b c R := by
  letI := alg c iK
  exact (by with_unfolding_all exact ((congrArg₂ (DatCopy.setIo (real3 c R)) (thriceY_eq b c R) (thriceX_eq b c R)) :))

theorem inertTransport_twice_heq_direct : HEq (real3 (a := b) c (iK := alg b iK) (real3 b R)) (real3 c R) :=
  (by with_unfolding_all exact ((HEq.symm (heq_of_eq (thrice_eq b c R))) :))

end Three

section Copy

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}
  {T : TwDat B} {Wt : Set B.places.Pl}

theorem coreJ_heq {k₀ : Formalism.L2.Pj.CoreJ a.D} {k : Formalism.L2.Pj.CoreJ b.D} (h : HEq k (coreJ b k₀)) : HEq (coreJ c k) (coreJ c k₀) := by
  obtain rfl : k = coreJ b k₀ := eq_of_heq h
  exact (by with_unfolding_all exact ((HEq.refl (coreJ c k₀)) :))

theorem realAdelicInertTransport_heq_of_transport (z₀ : Dat a.st I hX T Wt) (Xg : Finset (Gc B px → B.LL)) (tr : TrI B px) (k : Formalism.L2.Pj.CoreJ b.D)
    (i : Algebra k.Q.c.F b.D.what₂.LL) (hi : ∀ y : k.Q.c.F, B.embLL (algebraMap k.Q.c.F b.D.what₂.LL y) = (y : ℂ))
    (R : Links.RealDat3 b.D (famR b.st I hX (usedOf I T Wt) Xg tr) k.Q.c.F) (hXg : Xg = z₀.Xg)
    (htr : tr = z₀.tr) (hc : HEq k (coreJ b z₀.core)) (hR : HEq R (real3 b (iK := z₀.alg) z₀.R)) :
    HEq (real3 c (iK := i) R) (real3 c (iK := z₀.alg) z₀.R) := by
  subst hXg htr
  obtain rfl : k = coreJ b z₀.core := eq_of_heq hc
  have ha : i = (by with_unfolding_all exact ((alg b z₀.alg) :)) :=
    Algebra.algebra_ext _ _ fun y => (by with_unfolding_all exact ((B.embLL.injective ((hi y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((y))).symm : _)))) :
      _ = (@algebraMap _ _ _ _ z₀.alg ((by with_unfolding_all exact (y :))) : B.LL)) :))
  subst ha
  have hR' : R = (by with_unfolding_all exact ((real3 b (iK := z₀.alg) z₀.R) :)) := eq_of_heq ((by with_unfolding_all exact (hR :)))
  subst hR'
  exact (by with_unfolding_all exact ((inertTransport_twice_heq_direct b c (iK := z₀.alg) z₀.R) :))

end Copy

section Move

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o o' : q.Over}

theorem coreP_transfer {Z Z' : w.Lt} (s : SameGrp (B := B) (C := w.C) Z Z') {z : Dat (w.st Z) w.I hX T Wt} (h : CoreP z) :
    CoreP (w := w) (Z := Z') (Dat.transfer (B := B) (C := w.C) (a := Z) (b := Z') s z) := by
  unfold CoreP at h ⊢
  obtain ⟨laws, canon, dim, pb⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · with_unfolding_all exact Mv.lawsCore_tr (a := Z) Z' laws
  · with_unfolding_all exact canon
  · with_unfolding_all exact dim
  · with_unfolding_all exact pb

theorem copy_transfer (s : SameGrp (B := B) (C := w.C) o.Z o'.Z) {m : Moved o} {m' : Moved o'} (hm : m.Copy)
    (e : m'.z = Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z) : m'.Copy := by
  have h1 := coreJ_heq (a := Z₀) o.Z o'.Z (k₀ := z₀.core) (k := m.z.core) ((by with_unfolding_all exact (hm.core :)))
  have h2 := realAdelicInertTransport_heq_of_transport (a := Z₀) o.Z o'.Z z₀ m.z.Xg m.z.tr m.z.core m.z.alg m.z.alg_eq m.z.R m.Xg m.tr ((by with_unfolding_all exact (hm.core :))) ((by with_unfolding_all exact (hm.R :)))
  have e1 := congr_arg_heq (fun z : Dat (w.st o'.Z) w.I hX T Wt => z.core) e
  have e2 := congr_arg_heq (fun z : Dat (w.st o'.Z) w.I hX T Wt => z.R) e
  have h3 : HEq (Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z).core (coreJ (a := Z₀) o'.Z z₀.core) := (by with_unfolding_all exact (h1 :))
  have h4 : HEq (Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z).R (real3 (a := Z₀) o'.Z (iK := z₀.alg) z₀.R) := (by with_unfolding_all exact (h2 :))
  exact ⟨(by with_unfolding_all exact ((HEq.trans e1 h3) :)), (by with_unfolding_all exact ((HEq.trans e2 h4) :))⟩

theorem exists_moved_transfer (s : SameGrp (B := B) (C := w.C) o.Z o'.Z) (m : Moved o) (hm : m.Coh) :
    ∃ m' : Moved o', m'.z = Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z ∧ m'.Coh := by
  obtain ⟨y', hy⟩ := @GlobalTheory.Mem.R3.Rw.hd_tr B w.C o.Z o'.Z _ _ _ _ _ _ _ _ m.z.alg _ m.z.R.toRealDat m.y
  obtain ⟨t, a1, a2, a3, a4, a5, a6, a7⟩ := Mv.pkT_tr (a := o.Z) o'.Z (iK := m.z.alg) m.z.F m.y y' hy m.t
  have he := (@GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages B w.C o.Z o'.Z _ _ _ _ _ _ _ _ _ m.z.alg _ m.z.R m.z.F).1
  have hW := Dat.nonzeroIndexPlaces_transferAlongSameFiniteGroup (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z
  letI : Algebra m.z.core.Q.c.F (Late.D o'.Z).what₂.LL := alg (a := o.Z) o'.Z m.z.alg
  have hA : ((by with_unfolding_all exact (t.tA :)) : type_of% m.t.tA) = m.t.tA := eq_of_heq ((by with_unfolding_all exact (a1 :)))
  have b2 := HEq.trans hy.PY hm.PY
  have b3 := HEq.trans hy.PW hm.PW
  have b4 := HEq.trans a2 hm.rep
  have b5 := fun c => HEq.trans (a3 c) (hm.jE c)
  have b6 := fun c => HEq.trans (a4 c) (hm.jM c)
  have b7 := fun c => HEq.trans (a5 c) (hm.jX c)
  have b8 := HEq.trans a6 hm.eW
  have b9 := HEq.trans a7 hm.jMt
  have c1 := fun j v => (he j v).trans (m.eta j ((by with_unfolding_all exact (v :))))
  have c2 := fun F0 => (hW F0).symm.trans (m.W1 ((by with_unfolding_all exact (F0 :))))
  have c3 := fun c u => HEq.trans (heq_of_eq (congrArg (fun r : type_of% m.t.tA => (r c u).j) hA)) (m.tA c u)
  refine ⟨{ z := Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z
            intersectionNumber_baseChange := (by with_unfolding_all exact ((Dat.holds_transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.intersectionNumber_baseChange) :))
            exAt := (by with_unfolding_all exact ((Dat.exAt_transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.exAt) :))
            inGeo := (by with_unfolding_all exact ((Dat.inGeo_transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.inGeo) :))
            Xg := (by with_unfolding_all exact (m.Xg :))
            tr := (by with_unfolding_all exact (m.tr :))
            core := fun h => coreP_transfer s (m.core h)
            eta := (by with_unfolding_all exact (c1 :))
            W1 := (by with_unfolding_all exact (c2 :))
            y := (by with_unfolding_all exact ((Mv.hd3 (a := o.Z) o'.Z (iK := m.z.alg) m.y y') :))
            tup := (by with_unfolding_all exact (m.tup :))
            t := (by with_unfolding_all exact (t :))
            tA := (by with_unfolding_all exact (c3 :)) }, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact (hm.tupT :))
  · exact (by with_unfolding_all exact (b2 :))
  · exact (by with_unfolding_all exact (b3 :))
  · exact (by with_unfolding_all exact (b4 :))
  · exact (by with_unfolding_all exact (b5 :))
  · exact (by with_unfolding_all exact (b6 :))
  · exact (by with_unfolding_all exact (b7 :))
  · exact (by with_unfolding_all exact (b8 :))
  · exact (by with_unfolding_all exact (b9 :))

end Move

theorem exists_moved_loc : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (L : LocAll (lay0 (Dof x))), ∃ m : Moved (oL x L), m.z = datL x L ∧ m.Copy ∧ m.Coh := by
  intro K B f T w P x L
  obtain ⟨m, h1, h2⟩ := exists_moved_transfer (o := x.o) (o' := oL x L) (sameL x L) x.m x.coh
  exact ⟨m, h1, copy_transfer (o := x.o) (o' := oL x L) (sameL x L) x.copy h1, h2⟩

end GlobalTheory.HeightCounting.Fin3.MvLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherPlacesGroupContainsChartLevelsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.furtherPlaces_group_contains_chart_levels : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∃ (W : ∀ v, v ∈ Q → Subgroup (GL (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))) (ψ : (∀ v : Q, ↥(W v.1 v.2)) →* ℂˣ), (∀ v hv, W v hv ≤ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0) ∧ (∀ v hv, ∃ n : ℕ, 0 < n ∧ ∀ x, Formalism.L2.Herm.InPrinc (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) v n Lb0 x → x ∈ W v hv) ∧ (∀ β v hv, (K β).lev.Uloc v ≤ (W v hv).map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) ∧ (∀ β v hv, ((((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (W v hv)).FiniteIndex) ∧ (∀ β (κ : (K β).lev.U) (z : ∀ v : Q, ↥(W v.1 v.2)), (∀ v : Q, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (z v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) → (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ψ z) := by
  first | exact @GlobalTheory.Mem.Col2.TC.further_group_charts | exact GlobalTheory.Mem.Col2.TC.further_group_charts | (intros; apply GlobalTheory.Mem.Col2.TC.further_group_charts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GapRAllSt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.Up.GapAllStates

theorem gapR_allSt : AllSt fun _ _ _ _ _ _ x => ∀ (τ : (Dof x).what₂.Tau) (n : ℕ), n + 1 < (Dof x).R.r →
    100 * ((Dof x).R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt ((Dof x).hc τ) n - Formalism.L2.NTheta.lamAt ((Dof x).hc τ) (n + 1) :=
  Step.of_evG (EvG.imp (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)
    fun _ _ _ _ _ hK _ _ _ hO _ _ _ w _ _ x => (hK (w.st x.o.Z) hO).1.gapR)

end GlobalTheory.HeightCounting.Up.GapAllStates
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GroupTieOfLocalCoefficient
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HeightCounting.Fin3

theorem grpTie_of_LC : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (_ : LC hL x), Formalism.L2.DIV.GrpTie (Dof x)
      (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A x.m.z.F.P0 x.m.z.F.ψ0 x.m.z.F.P1 x.m.z.F.ψ1
      (x.m.z.R.eG.trans x.m.z.cG) := by
  intro hL K B f T w P x l
  have hc := GlobalTheory.Mem.R3.pins_card_index_ranks _ _ _ _ _ _ _ _ _ _ x.m.z.pins
  have hU : (Dof x).nexp.U = Formalism.IndefR.NX.U (Dof x).nd := l.b.Bs.exp.U_eq
  obtain ⟨_, _, _, he0, _, _⟩ := x.m.z.pins.keep.grp
  refine ⟨hc.1, he0, ?_, ?_, hc.2.1, x.m.z.pins.keep.psi.lvl⟩
  · intro g
    rw [hU]
    exact l.rat.rat.lvl g
  · intro u hu i b
    have hu' : (x.m.z.R.eG.trans x.m.z.cG) u ∈ Formalism.IndefR.NX.U (Dof x).nd := hU ▸ hu
    refine ⟨psiUOf (Dof x).nd (NX.xiRed (Dof x)) l.rat.In.θ ⟨_, hu'⟩, l.rat.rat.psi u hu', ?_⟩
    exact l.b.Bs.psiU i b _ hu hu'

end GlobalTheory.HeightCounting.Fin3
end

