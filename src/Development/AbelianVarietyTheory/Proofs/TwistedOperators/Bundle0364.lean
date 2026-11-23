module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsRigIsoOfBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

noncomputable section

namespace GlobalTheory.RigIsoDescent

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A}

theorem exists_isRigIso_of_gen {Y : Scheme.{0}} {x x' : Y ⟶ S} {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left}
    {k : ℤ} (hΨ : IsPointed A Ψ) (t : LB.Gen (isoLB A L Ψ k)) (ht : t.IsGen) : ∃ β, IsRigIso A L Ψ k β := by
  obtain ⟨β, hβ, hc⟩ := DVR.exists_normalized_to L.isLB _ _ t ht (fst (Over.mk x) A).left
    (ptSecT A (1 : Over.mk x ⟶ A)).left ThetaReal.NormMul.ptSec_fst _ _
    (LB.mulGen L.L (Y := Y) _ _ _ _ (rigT A L.L L.rig (Over.mk x) k) (rigT A L.L L.rig (Over.mk x') (-1)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (ThetaReal.NormMul.rigT_isGen L.rigGen _) (ThetaReal.NormMul.rigT_isGen L.rigGen _))
    (by
      rw [DVR.fsum_sumElim, DVR.fsum, DVR.fsum, DVR.fsum, Fin.sum_univ_two, Fin.sum_univ_one, Fin.sum_univ_one]
      refine congrArg₂ (· + ·) (congrArg (Finsupp.single · k) ThetaReal.NormMul.ptSec_snd)
        (congrArg (Finsupp.single · (-1 : ℤ)) ?_)
      refine (Category.assoc _ _ _).symm.trans ?_
      rw [hΨ.2]
      exact ThetaReal.NormMul.ptSec_snd)
  exact ⟨β, hΨ, hβ, hc⟩

theorem exists_gen_of_field (hA : IsAbelianScheme A) {K K' : Type} [Field K] [Field K'] (φ : K →+* K')
    {x x' : Sp K ⟶ S} {w w' : Sp K' ⟶ S} {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left}
    {Ψ' : (Over.mk w ⊗ A).left ⟶ (Over.mk w' ⊗ A).left} {k : ℤ} (hw : w = spMap φ ≫ x)
    (π : (Over.mk w ⊗ A).left ⟶ (Over.mk x ⊗ A).left)
    (h₁ : π ≫ (fst (Over.mk x) A).left = (fst (Over.mk w) A).left ≫ spMap φ)
    (h₂ : π ≫ (snd (Over.mk x) A).left = (snd (Over.mk w) A).left)
    (h₃ : π ≫ Ψ ≫ (snd (Over.mk x') A).left = Ψ' ≫ (snd (Over.mk w') A).left)
    (t : LB.Gen (isoLB A L Ψ' k)) (ht : t.IsGen) : ∃ u : LB.Gen (isoLB A L Ψ k), u.IsGen := by
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  let p : (Over.mk x ⊗ A).left ⟶ Sp K := (fst (Over.mk x) A).left
  have H₀ : IsPullback (snd (Over.mk x) A).left p A.hom x := (IsPullback.of_hasPullback x A.hom).flip
  have H₁ : IsPullback (snd (Over.mk w) A).left (fst (Over.mk w) A).left A.hom w :=
    (IsPullback.of_hasPullback w A.hom).flip
  have : IsProper p := MorphismProperty.of_isPullback (P := @IsProper) H₀ inferInstance
  have : GeometricallyIntegral p := MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H₀ inferInstance
  have H : IsPullback π (fst (Over.mk w) A).left p (spMap φ) :=
    IsPullback.of_right (by rw [h₂, ← hw]; exact H₁) h₁ H₀
  obtain ⟨c, hc⟩ := gen_chartPull (chartPullOut L.L (isoφ A Ψ) ![k, -1] π (isoφ A Ψ') fun i => by
    fin_cases i
    exacts [h₂.symm, h₃.symm]) t ht
  exact FieldTriv.exists_gen_of_isPullback φ p π _ H (LB.isLB_linComb L.isLB _ _) c hc

end General

theorem eSec_fst {B B' : Scheme.{0}} (u : B' ⟶ B) (A : Over B) [GrpObj A] :
    eSec ((Over.pullback u).obj A) ≫ pullback.fst A.hom u = u ≫ eSec A := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem ptSec_swap {K : Type} [CommRing K] (x : Sp K ⟶ Xo.X) :
    (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ (swap x).hom = eSec (Fib Xo x) := by
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (swap_hom_fst x)).trans
      (ThetaReal.NormMul.ptSec_snd.trans (eSec_fst x _).symm))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (swap_hom_snd x)).trans
      (ThetaReal.NormMul.ptSec_fst.trans (Over.w η[Fib Xo x]).symm))

theorem isPointed_of_isMonHom {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x')
    (hf : IsMonHom f) : IsPointed Xo.univ.t.G (conj x x' f.left) := by
  refine ⟨(over_iff _).2 (Over.w f), ?_⟩
  have e : eSec (Fib Xo x) ≫ f.left = eSec (Fib Xo x') := congrArg (fun q => q.left) hf.one_hom
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (ptSec_swap x)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans ?_)))
  exact (Iso.comp_inv_eq _).2 (ptSec_swap x').symm

theorem exists_isRigIso_of_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') (k : ℤ), IsBC φ f g → IsMonHom f → (∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj w w' g.left) k β) → ∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) k β := by
  rintro E _ _ _ H Dw l Xo K L _ _ φ x x' w w' f g k ⟨hw, hw', hbc⟩ hf ⟨β, -, hβ, -⟩
  have mk : ∀ {y : Sp K ⟶ Xo.X} {v : Sp L ⟶ Xo.X}, v = spMap φ ≫ y →
      ∃ π : pullback Xo.univ.t.G.hom v ⟶ pullback Xo.univ.t.G.hom y,
        π ≫ pullback.fst _ _ = pullback.fst _ _ ∧ π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ := fun h =>
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap φ) (by rw [Category.assoc, ← h, pullback.condition]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨π, a₁, a₂⟩ := mk hw
  obtain ⟨π', b₁, b₂⟩ := mk hw'
  have e := hbc π π' a₁ a₂ b₁ b₂
  have hp := isPointed_of_isMonHom f hf
  obtain ⟨u, hu⟩ := exists_gen_of_field (L := Xo.univ.t.PP) (Ψ := conj x x' f.left) (UnivPol.pol Xo).isAb φ hw
    ((swap w).hom ≫ π ≫ (swap x).inv)
    (by rw [Category.assoc, Category.assoc, swap_inv_fst, a₂, swap_hom_snd_assoc])
    (by rw [Category.assoc, Category.assoc, swap_inv_snd, a₁, swap_hom_fst])
    (by
      simp only [conj_apply, Category.assoc, Iso.inv_hom_id_assoc, swap_inv_snd]
      rw [← reassoc_of% e, b₁]) β hβ
  exact exists_isRigIso_of_gen hp u hu

end GlobalTheory.RigIsoDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

theorem hTens_eq_trace {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α]
    [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    GlobalTheory.WeilM.hTens c JA JB x y = (xᵀ * JA * y.map c * JBᵀ).trace := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ i, ∑ k, ∑ l, x i j * JA i k * JB j l * c (y k l)
      = ∑ i, ∑ l, ∑ k, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ k, x i j * JA i k * JB j l * c (y k l) := Finset.sum_comm
    _ = ∑ l, ∑ k, ∑ i, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun i _ => ?_
        ring

theorem hTens_transpose_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] (e : α ≃ γ) (K : Matrix α α A) {G H : Matrix β β A} (x : A)
    (hGH : H * G = 1) (hG : G.map c = Gᵀ) (u u' : Matrix β γ A) :
    GlobalTheory.WeilM.hTens c Kᵀ (x • H) (uᵀ.submatrix e id * G) (u'ᵀ.submatrix e id * G) =
      -GlobalTheory.WeilM.hTens c (-G) (x • reindex e e Kᵀ) u u' := by
  have hHG : Gᵀ * Hᵀ = 1 := by rw [← Matrix.transpose_mul, hGH, Matrix.transpose_one]
  have hmap : (u'ᵀ.submatrix e id * G).map c = (u'ᵀ.submatrix e id).map c * Gᵀ := by
    rw [← hG]
    exact Matrix.map_mul (f := (c : A →+* A))
  have hM : ((u'ᵀ.submatrix e id).map c)ᵀ * K * uᵀ.submatrix e id = u'.map c * reindex e e K * uᵀ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id,
      Matrix.reindex_apply]
    refine Fintype.sum_equiv e _ _ fun a => ?_
    congr 1
    exact Fintype.sum_equiv e _ _ fun b => by simp
  rw [hTens_eq_trace, hTens_eq_trace, hmap, Matrix.transpose_mul, Matrix.transpose_smul]
  calc (Gᵀ * (uᵀ.submatrix e id)ᵀ * Kᵀ * ((u'ᵀ.submatrix e id).map c * Gᵀ) * (x • Hᵀ)).trace
      = x * (Gᵀ * (uᵀ.submatrix e id)ᵀ * Kᵀ * (u'ᵀ.submatrix e id).map c * (Gᵀ * Hᵀ)).trace := by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
        simp only [Matrix.mul_assoc]
    _ = x * (Gᵀ * (uᵀ.submatrix e id)ᵀ * Kᵀ * (u'ᵀ.submatrix e id).map c).trace := by
        rw [hHG, Matrix.mul_one]
    _ = x * (((u'ᵀ.submatrix e id).map c)ᵀ * K * uᵀ.submatrix e id * G).trace := by
        congr 1
        rw [← Matrix.trace_transpose]
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = x * (u'.map c * reindex e e K * uᵀ * G).trace := by rw [hM]
    _ = x * (uᵀ * G * u'.map c * reindex e e K).trace := by
        rw [Matrix.mul_assoc (u'.map c * reindex e e K), Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
    _ = -((uᵀ * -G * u'.map c * (x • reindex e e Kᵀ)ᵀ).trace) := by
        rw [Matrix.transpose_smul, Matrix.transpose_reindex, Matrix.transpose_transpose, Matrix.mul_neg,
          Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_smul, Matrix.trace_neg, Matrix.trace_smul, neg_neg,
          smul_eq_mul]

theorem exists_darboux_transpose_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β γ κ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype κ] [DecidableEq β] (e : α ≃ γ) (K : Matrix α α A)
    {G H : Matrix β β A} (x : A) (hGH : H * G = 1) (hG : G.map c = Gᵀ) {JV JB : Matrix β β A} {JW : Matrix γ γ A}
    {JA : Matrix α α A} (hV : JV = -G) (hW : JW = x • reindex e e Kᵀ) (hA : JA = Kᵀ) (hB : JB = x • H)
    (M : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c (-1) JV JW) κ) (T : Matrix β γ A ≃+ Matrix α β A)
    (hT : ∀ u, T u = uᵀ.submatrix e id * G) :
    ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c 1 JA JB) κ, ∀ u, co.e (T u) = M.e u := by
  subst hV hW hA hB
  have hsmul : ∀ (r : R) (u : Matrix β γ A), T (r • u) = r • T u := by
    intro r u
    rw [hT, hT, Matrix.transpose_smul]
    exact Matrix.smul_mul r (uᵀ.submatrix e id) G
  have h1 : ∀ v, (T.toLinearEquiv hsmul).symm (T v) = v := fun v => (T.toLinearEquiv hsmul).symm_apply_apply v
  refine ⟨{ e := (T.toLinearEquiv hsmul).symm.trans M.e, form := ?_ }, ?_⟩
  · intro w w'
    obtain ⟨u, rfl⟩ := T.surjective w
    obtain ⟨u', rfl⟩ := T.surjective w'
    simp only [LinearEquiv.trans_apply]
    rw [h1, h1, ← M.form]
    simp only [GlobalTheory.WeilM.symp]
    rw [hT, hT, hTens_transpose_mul c e K x hGH hG, one_mul, neg_one_mul]
  · intro u
    simp only [LinearEquiv.trans_apply]
    rw [h1]

theorem map_transpose_inv_mul {E A : Type} [CommRing E] [CommRing A] (f : E →+* A) {α β γ : Type} [Fintype β]
    [DecidableEq β] (e : α ≃ γ) (x : Matrix α β E) {G : Matrix β β E} (hG : IsUnit G.det) :
    (((x * G⁻¹)ᵀ.submatrix id e.symm).map f)ᵀ.submatrix e id * G.map f = x.map f := by
  have h1 : (((x * G⁻¹)ᵀ.submatrix id e.symm).map f)ᵀ.submatrix e id = (x * G⁻¹).map f := by
    ext a b
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq, Equiv.symm_apply_apply]
  rw [h1, ← Matrix.map_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul G hG, Matrix.mul_one]

private theorem symp_smul_eq_symp_one_smul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type}
    [Fintype α] [Fintype β] (ξ : A) (JA : Matrix α α A) (JB : Matrix β β A) (w w' : Matrix α β A) :
    GlobalTheory.WeilM.symp c ξ JA JB w w' = GlobalTheory.WeilM.symp c 1 JA (ξ • JB) w w' := by
  simp only [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, one_mul, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring


set_option maxHeartbeats 800000 in
theorem exists_darboux_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∃ (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) (Fin S.rank × Fin d)),
        ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹) ∧
        (∀ x : Matrix (Fin X.rank) (Fin S.rank) D.host.E, ∃ y z : Fin S.rank × Fin d → D.host.F,
          co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
            (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) ∧
        ∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ),
          IsDatum M ψ cS Φ f ↔
            Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d) ∧ GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ = f := by
  intro D ψ θ _ ε S X A B d e Bs _ _ Vs Ws r s r' s' hJ hJW hV _ _ M hM cS hcS
  have hsgn : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
    cases ε <;> ext i j <;> simp [Formalism.BasicNotions.HSpace.gram]
  have hdet : IsUnit (sgn ε S).gram.det := isUnit_iff_ne_zero.mpr (Formalism.L2.Theta.gram_det_ne _)
  have hG0 : (sgn ε S).gram = -Vs.J := by
    rw [hsgn, hJ]
    cases ε <;> simp
  have hmapc : ∀ {m n : Type} (J : Matrix m n D.host.E),
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (J.map D.sp.cm.sig) := by
    intro m n J
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  have hGJ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J = -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram := by
    rw [hG0]
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hG : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram)ᵀ := by
    rw [hmapc, hG0]
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hV.herm]
  have hGH : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F ((sgn ε S).gram)⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0 •
      reindex e e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram)ᵀ := by
    rw [hJW]
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.reindex_apply, map_mul]
  have hT : ∀ u, cS u = uᵀ.submatrix e id * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram := by
    intro u
    rw [hcS u, hsgn]
  obtain ⟨co0, hco0⟩ := exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0)
    hGH hG hGJ hW rfl rfl M.co cS hT
  obtain ⟨co, hco⟩ : ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F ((sgn ε S).gram)⁻¹))
      (Fin S.rank × Fin d), (∀ u, co.e (cS u) = M.co.e u) ∧ ∀ w, co.e w = co0.e w := by
    refine ⟨⟨co0.e, fun w w' => ?_⟩, hco0, fun _ => rfl⟩
    rw [← co0.form, symp_smul_eq_symp_one_smul]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.transpose_map]
  refine ⟨Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0, ((sgn ε S).gram)⁻¹, co, ?_, ?_, ?_⟩
  · ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, map_mul]
  · intro y
    obtain ⟨a, b, hab⟩ := hM.rat ((y * ((sgn ε S).gram)⁻¹)ᵀ.submatrix id e.symm)
    refine ⟨a, b, ?_⟩
    have hu : cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F ((y * ((sgn ε S).gram)⁻¹)ᵀ.submatrix id e.symm)) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F y := by
      rw [hT]
      exact map_transpose_inv_mul _ e y hdet
    rw [← hu, hco.1]
    exact hab
  · intro Φ f
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, funext fun w => ?_⟩
      obtain ⟨u, rfl⟩ := cS.surjective w
      rw [← h2 u]
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hco.1 u]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun u => ?_⟩
      rw [← h2]
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hco.1 u]

end GlobalTheory.SquareAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalIsometryOfTraceSimilitudeSq
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.TraceSimilitude

theorem trace_natSq_mul {E : Type} [Field E] [NumberField E] (N : ℕ) (x : E) :
    Algebra.trace ℚ E ((N : E) ^ 2 * x) = (N : ℚ) ^ 2 * Algebra.trace ℚ E x := by
  have h : ((N : E) ^ 2) = algebraMap ℚ E ((N : ℚ) ^ 2) := by simp
  rw [h, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem exists_gl_of_trace_similitude : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ), 0 < N → (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) → ∀ (gam : X.Λ →ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (gam u : Fin r → E) (gam v : Fin r → E)) = (N : ℚ) ^ 2 * Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (u : Fin r → E) (v : Fin r → E))) → (∀ w : X'.Λ, ∃ v, gam v = (N ^ 2) • w) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (N : E) • ((a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E)) = (gam v : Fin r → E)) ∧ (∀ w ∈ X'.Λ, (N : E) • (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) ∈ X.Λ) ∧ ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * herm X.Gm u v := by
  classical
  intro E _ _ _ r X X' N hN hn gam htr hsurj
  have hs : Submodule.span E (Set.range X.Λ.subtype) = ⊤ := by
    rw [← X.Λ_span]; congr 1; exact Subtype.range_coe
  have hs' : Submodule.span E (Set.range X'.Λ.subtype) = ⊤ := by
    rw [← X'.Λ_span]; congr 1; exact Subtype.range_coe
  obtain ⟨A, hA⟩ := FrameFibre.exists_matrix X.Λ.subtype X.Λ.injective_subtype hs
    (X'.Λ.subtype ∘ₗ gam)
  have hA' : ∀ v : X.Λ, A *ᵥ (v : Fin r → E) = (gam v : Fin r → E) := hA
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hcoe : ∀ w : X'.Λ, (((N ^ 2) • w : X'.Λ) : Fin r → E) = ((N : E) ^ 2) • (w : Fin r → E) := by
    intro w
    rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul E]
    push_cast; rfl
  have hsurjA : Function.Surjective (Matrix.toLin' A) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs', Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := hsurj w
    refine ⟨((N : E) ^ 2)⁻¹ • (v : Fin r → E), ?_⟩
    rw [map_smul, Matrix.toLin'_apply, hA', hv, hcoe, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hN0), one_smul]
    rfl
  have hU : IsUnit A := Matrix.mulVec_surjective_iff_isUnit.1 hsurjA
  set U := hU.unit with hUdef
  have hUA : (U : Matrix (Fin r) (Fin r) E) = A := hU.unit_spec
  let a : GL (Fin r) E :=
    ⟨(N : E)⁻¹ • A, (N : E) • ((U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E),
      by rw [smul_mul_smul_comm, inv_mul_cancel₀ hN0, one_smul, ← hUA, U.mul_inv],
      by rw [smul_mul_smul_comm, mul_inv_cancel₀ hN0, one_smul, ← hUA, U.inv_mul]⟩
  have ha : (a : Matrix (Fin r) (Fin r) E) = (N : E)⁻¹ • A := rfl
  have hai : ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) =
      (N : E) • ((U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := rfl
  obtain ⟨ε, hε, hξ⟩ : ∃ ε : E, (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 := by
    rcases TraceIsometry.eq_or_eq_neg_of_norm_eq X.ξ0_im X'.ξ0_im hn with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, _root_.one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_mul]⟩
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
  have h1 : cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
  have key : ∀ u v : X.Λ, herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) =
      (N : E) ^ 2 * ε * herm X.Gm u v := by
    intro u v
    have h0 : -X'.ξ0 * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) -
        (N : E) ^ 2 * (-X.ξ0 * herm X.Gm u v) = 0 := by
      refine FrameFibre.eq_zero_of_trace _ fun b => ?_
      have h2 := htr (b • u) v
      have h3 : ((b • u : X.Λ) : Fin r → E) = (b : E) • (u : Fin r → E) := rfl
      have h4 := FrameFibre.herm_smul_smul X'.Gm (b : E) 1 (A *ᵥ (u : Fin r → E))
        (A *ᵥ (v : Fin r → E))
      have h5 := FrameFibre.herm_smul_smul X.Gm (b : E) 1 (u : Fin r → E) (v : Fin r → E)
      rw [one_smul, h1, _root_.mul_one] at h4 h5
      rw [← hA', ← hA', h3, Matrix.mulVec_smul, h4, h5] at h2
      have e1 : (b : E) * (-X'.ξ0 * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E))) =
          -X'.ξ0 * ((b : E) * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E))) := by ring
      have e2 : (b : E) * ((N : E) ^ 2 * (-X.ξ0 * herm X.Gm u v)) =
          (N : E) ^ 2 * (-X.ξ0 * ((b : E) * herm X.Gm u v)) := by ring
      rw [mul_sub, map_sub, e1, e2, trace_natSq_mul, h2, sub_self]
    rw [hξ] at h0
    apply mul_left_cancel₀ X.ξ0_ne
    linear_combination (-ε) * h0 -
      (X.ξ0 * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E))) * hε2
  have keyA : ∀ x y : Fin r → E, herm X'.Gm (A *ᵥ x) (A *ᵥ y) = (N : E) ^ 2 * ε * herm X.Gm x y := by
    intro x y
    obtain ⟨c, v, hc, hv⟩ := FrameFibre.exists_smul_eq X.Λ.subtype hs x
    obtain ⟨d, w, hd, hw⟩ := FrameFibre.exists_smul_eq X.Λ.subtype hs y
    have h2 := key v w
    rw [Submodule.subtype_apply] at hv hw
    rw [← hv, ← hw, Matrix.mulVec_smul, Matrix.mulVec_smul, FrameFibre.herm_smul_smul,
      FrameFibre.herm_smul_smul] at h2
    have hc' : (c : E) ≠ 0 := by simpa using hc
    have hd' : cc (d : E) ≠ 0 := (map_ne_zero (IsCMField.complexConj E)).2 (by simpa using hd)
    apply mul_left_cancel₀ (mul_ne_zero hc' hd')
    linear_combination h2
  refine ⟨a, ε, hε, hξ, fun v => ?_, fun w hw => ?_, fun x y => ?_⟩
  · rw [ha, Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hN0, one_smul, hA']
  · obtain ⟨v, hv⟩ := hsurj ⟨w, hw⟩
    have h3 : (U : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) = (N : E) ^ 2 • w := by
      rw [hUA, hA', hv, hcoe]
    have h2 : ((U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((N : E) ^ 2 • w) = v := by
      rw [← h3, Matrix.mulVec_mulVec, U.inv_mul, Matrix.one_mulVec]
    rw [hai, Matrix.smul_mulVec, smul_smul, ← pow_two, ← Matrix.mulVec_smul, h2]
    exact v.2
  · have hcc : cc ((N : E)⁻¹) = (N : E)⁻¹ :=
      (map_inv₀ (IsCMField.complexConj E) _).trans (by rw [map_natCast])
    rw [ha, Matrix.smul_mulVec, Matrix.smul_mulVec, FrameFibre.herm_smul_smul, hcc,
      keyA]
    field_simp

end GlobalTheory.TraceSimilitude
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalPointThetaGeneratorNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaNZ

theorem exists_ratPt_sv_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x₁ : Sp Ω ⟶ Xo.X} {s : LB.Sec (PPx x₁)}, IsThGen x₁ s → ∃ w : Sp Ω ⟶ Gx x₁, w ≫ (fst (Over.mk x₁) Xo.univ.t.G).left = 𝟙 _ ∧ ∀ (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s w z J ≠ 0 := by
  intro E _ _ _ H Dw l Xo Ω _ _ x₁ s hs
  have hnz := GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo Ω x₁ s hs
  obtain ⟨q, i, -, hqi⟩ := hnz (IsLocalRing.closedPoint Ω)
  have := Xo.univ.t.semi.smooth
  have : Smooth (fst (Over.mk x₁) Xo.univ.t.G).left := by
    show Smooth (pullback.fst x₁ Xo.univ.t.G.hom)
    infer_instance
  have : JacobsonSpace ↥(Over.mk x₁).left := inferInstanceAs (JacobsonSpace (PrimeSpectrum Ω))
  have : JacobsonSpace ↥(Gx x₁) := LocallyOfFiniteType.jacobsonSpace (fst (Over.mk x₁) Xo.univ.t.G).left
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints ⟨q, hqi⟩
    ((Gx x₁).basicOpen (s.f i)).isOpen.isLocallyClosed
  have hyc' : IsClosed ({y} : Set (Gx x₁)) := hyc
  refine ⟨pointOfClosedPoint (fst (Over.mk x₁) Xo.univ.t.G).left y hyc',
    pointOfClosedPoint_comp _ y hyc', fun z J hJ => ?_⟩
  set w := pointOfClosedPoint (fst (Over.mk x₁) Xo.univ.t.G).left y hyc'
  have hwz : w z = y := pointOfClosedPoint_apply _ y hyc' z
  let φ : Fin 1 → (Gx x₁ ⟶ Xo.univ.t.G.left) := fun _ => (snd (Over.mk x₁) Xo.univ.t.G).left
  have hi : w z ∈ LB.wchart Xo.univ.t.PP.L φ i := by
    rw [hwz]; exact Scheme.basicOpen_le _ _ hy
  have hj := hJ.mem φ w
  show sval s w z J ≠ 0
  rw [sval_of s w z J (fun k => J (w ≫ φ k)) (fun k => rfl), sec_trans s w z hj hi]
  have hU : IsUnit (gs w z (LB.wchart Xo.univ.t.PP.L φ i) (s.f i)) := by
    have hb : z ∈ (Sp Ω).basicOpen ((w.app _).hom (s.f i)) := by
      rw [← Scheme.preimage_basicOpen]
      show w z ∈ (Gx x₁).basicOpen (s.f i)
      rw [hwz]; exact hy
    convert ((Sp Ω).mem_basicOpen _ z hi).1 hb using 1
    exact gs_eq w z _ hi _
  exact ((Units.isUnit _).mul hU).ne_zero

end GlobalTheory.ThetaNZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSpacesIsometricOfRankSignatureStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSpaces_isometric_of_rank_signature : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D := by
  first | exact @GlobalTheory.RationalIsometry.rationalSt | exact GlobalTheory.RationalIsometry.rationalSt | (intros; apply GlobalTheory.RationalIsometry.rationalSt <;> assumption)
end

