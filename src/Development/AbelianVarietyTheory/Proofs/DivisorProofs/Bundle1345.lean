module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvolutionFixesPolynomialImage
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.NormHasseFixed

theorem cT_aeval {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    cT σ (aeval A p) = aeval (cT σ A) (p.map σ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), ← hp, ← hq]
    ext i j; simp [cT]
  | monomial k a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def]
    unfold cT
    rw [Matrix.map_smul' _ _ _ (fun x y => map_mul σ x y), Matrix.map_pow, Matrix.transpose_smul, Matrix.transpose_pow]

theorem aeval_mulVec {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ} (N : Matrix (Fin n) (Fin n) L)
    (μ : L) (v : Fin n → L) (hv : N *ᵥ v = μ • v) (p : K[X]) : (aeval N p) *ᵥ v = aeval μ p • v := by
  have hpow : ∀ k : ℕ, (N ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mulVec, hp, hq, add_smul]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, Matrix.smul_mulVec, hpow,
      smul_assoc]

theorem aeval_inv_map_eq {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (γ : GL (Fin n) E)
    (hγ : cT σ γ.val * 1 * γ.val = 1) (m : E[X]) (hm : cT σ (aeval γ.val m) = aeval γ.val m)
    {L : Type} [Field L] [Algebra E L] (α : L) (hα0 : α ≠ 0) (hroot : aeval α γ.val.charpoly = 0) :
    aeval α⁻¹ (m.map σ) = aeval α m := by
  have hU' : cT σ γ.val = (γ⁻¹).val := by
    have h := congrArg (· * (γ⁻¹).val) hγ
    simpa [Matrix.mul_assoc] using h
  rw [aeval_def, ← eval_map, ← Matrix.charpoly_map, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hroot
  have hAv : (γ.val.map (algebraMap E L)) *ᵥ v = α • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hBA : ((γ⁻¹).val.map (algebraMap E L)) * (γ.val.map (algebraMap E L)) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBv : ((γ⁻¹).val.map (algebraMap E L)) *ᵥ v = α⁻¹ • v := by
    have h : ((γ⁻¹).val.map (algebraMap E L)) *ᵥ ((γ.val.map (algebraMap E L)) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
    rw [hAv, Matrix.mulVec_smul] at h
    conv_rhs => rw [← h, smul_smul, inv_mul_cancel₀ hα0, one_smul]
  have hmap : ∀ (M : Matrix (Fin n) (Fin n) E) (p : E[X]),
      (aeval M p).map (algebraMap E L) = aeval (M.map (algebraMap E L)) p := by
    intro M p
    have h := aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId E L)) M p
    have e : (⇑(Algebra.ofId E L) : E → L) = algebraMap E L := rfl
    simpa [AlgHom.mapMatrix_apply, e] using h.symm
  have h1 : (cT σ (aeval γ.val m)).map (algebraMap E L) *ᵥ v = (aeval γ.val m).map (algebraMap E L) *ᵥ v := by
    rw [hm]
  rw [cT_aeval, hU', hmap, hmap, aeval_mulVec _ _ v hBv, aeval_mulVec _ _ v hAv] at h1
  exact smul_left_injective L hv0 h1


open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField in
theorem invol_mk_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X], cT (IsCMField.complexConj E).toRingEquiv.toRingHom (aeval γ.val m) = aeval γ.val m → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  intro E _ _ _ n γ hγ _ m hm r Q hQ
  have hγ' : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.val * 1 * γ.val = 1 := hγ
  have hroot : aeval (AdjoinRoot.root Q.1) γ.val.charpoly = 0 := by
    obtain ⟨c, hc⟩ := hQ
    rw [hc, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
  have h := aeval_inv_map_eq (IsCMField.complexConj E).toRingEquiv.toRingHom γ hγ' m hm (AdjoinRoot.root Q.1) (root_ne_zero Q) hroot
  rw [aeval_def, eval₂_map, AdjoinRoot.aeval_eq] at h
  refine Eq.trans ?_ h
  show AdjoinRoot.lift ((AdjoinRoot.of Q.1).comp (IsCMField.complexConj E : E →+* E)) (AdjoinRoot.root Q.1)⁻¹
    (eval₂_conj_inv_root Q) (AdjoinRoot.mk Q.1 m) = _
  rw [AdjoinRoot.lift_mk]
  rfl

end GlobalTheory.NormHasseFixed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfFiniteFibres
section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory

namespace GlobalTheory.FlagPlucker

theorem isAmpleLB_of_finite_fibres (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (hf : IsProper f)
    (ι : Type) [Fintype ι] (L : ι → LB X) (hL : ∀ i, (L i).IsLB) (M : ι → ℕ)
    (t : ∀ i, Fin (M i + 1) → (L i).Sec) (ht : ∀ i, ⨆ m, nonzeroLocus (t i m) = ⊤)
    (hfin : ∀ (K : Type) [Field K] [IsAlgClosed K] (a : Sp K ⟶ X),
      {a' : Sp K ⟶ X | a' ≫ f = a ≫ f ∧
        ∀ i, a' ≫ GlobalTheory.ProjSpace.toProj f (t i) (ht i) = a ≫ GlobalTheory.ProjSpace.toProj f (t i) (ht i)}.Finite)
    (w : ι → ℕ) (hw : ∀ i, 1 ≤ w i) (N : LB X) (hN : N.IsLB)
    (hcls : GlobalTheory.CechPic.cls N hN = ∑ i, w i • GlobalTheory.CechPic.cls (L i) (hL i)) : GlobalTheory.IsAmpleLB N := by
  obtain ⟨Q, Ψ, r, P, hP, hr, hΨ, hc, hinj⟩ :=
    GlobalTheory.AmpleSeparateOverRing.exists_ample_model R X f ι L hL M t ht w hw Finset.univ
  have : LocallyOfFiniteType (Ψ ≫ r) := by rw [hΨ]; infer_instance
  have : LocallyOfFiniteType Ψ := locallyOfFiniteType_of_comp Ψ r
  have : IsProper (Ψ ≫ r) := by rw [hΨ]; infer_instance
  have : IsProper Ψ := IsProper.of_comp Ψ r
  have : LocallyQuasiFinite Ψ := GlobalTheory.locallyQuasiFinite_of_finite_geometric_points Ψ fun K _ _ y => by
    by_cases hy : ∃ a : Spec (.of K) ⟶ X, a ≫ Ψ = y
    · obtain ⟨a, rfl⟩ := hy
      have hs : {a' : Spec (.of K) ⟶ X | a' ≫ Ψ = a ≫ Ψ}.Finite := (hfin K a).subset fun a' ha' => by
        obtain ⟨e1, e2⟩ := hinj K a' a ha'
        exact ⟨e1, fun i => e2 i (Finset.mem_univ i)⟩
      exact hs.to_subtype
    · haveI : IsEmpty {x : Spec (.of K) ⟶ X // x ≫ Ψ = y} := ⟨fun x => hy ⟨x.1, x.2⟩⟩
      infer_instance
  have := IsFinite.of_isProper_of_locallyQuasiFinite Ψ
  have hcls' : CechPic.cls (P.pull Ψ) (LB.isLB_pull hP.isLB Ψ) = CechPic.cls N hN := by
    rw [hc, hcls]
    exact Finset.sum_congr rfl fun i _ => natCast_zsmul _ _
  exact (isAmpleLB_congr (LB.isLB_pull hP.isLB Ψ) hN
    ((CechPic.cls_eq_iff _ _).1 hcls')).1 (hP.pull_of_isAffineHom Ψ)

end GlobalTheory.FlagPlucker

noncomputable section

namespace GlobalTheory.FlagPlucker

open GlobalTheory.FlagMod Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}


open Classical in
def ind (σ : E →+* ℂ) (m : ℕ) : Ix Dw → ℤ :=
  fun ix => ix.elim 0 fun p => if p.1 = σ ∧ (p.2 : ℕ) ≤ m then 1 else 0

def plkU (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ) :
    Matrix (Fin Mc.n) (Fin (Dw.mult σ)) Γ(Z, F.U k ⊓ π ⁻¹ᵁ Mc.U) :=
  (chg Mc (F.M k).toMChart).map (π.appLE (Mc.U ⊓ (F.M k).U) (F.U k ⊓ π ⁻¹ᵁ Mc.U)
      (fun _ hp => ⟨hp.2, F.le k hp.1⟩)).hom *
    (F.u k σ).map (resG Z (inf_le_left : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ F.U k))

def plkMinor (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ) (m : Fin (Dw.mult σ))
    (r : Fin ((m : ℕ) + 1) → Fin Mc.n) : Γ(Z, F.U k ⊓ π ⁻¹ᵁ Mc.U) :=
  ((plkU F Mc k σ).submatrix r (Fin.castLE m.2)).det

abbrev plkNum (Mc : MChart Y) (m : ℕ) : ℕ := Fintype.card (Fin (m + 1) → Fin Mc.n)

def plkIdx (Mc : MChart Y) (m : ℕ) : Fin (plkNum Mc m + 1) → Option (Fin (m + 1) → Fin Mc.n) :=
  Fin.cases none fun i => some ((Fintype.equivFin _).symm i)

theorem plk_le (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U)
    (e : Ix Dw → ℤ) (j : ((F.LL e).pull g).ι) :
    ((F.LL e).pull g).U j ≤ g ⁻¹ᵁ (F.U (j PUnit.unit) ⊓ π ⁻¹ᵁ Mc.U) :=
  fun _ hp => ⟨LB.wchart_le _ _ j PUnit.unit hp, hg trivial⟩

def plkLoc (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U)
    (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (q : Fin (plkNum Mc m + 1)) (j : ((F.LL (ind σ m)).pull g).ι) :
    Γ(T, ((F.LL (ind σ m)).pull g).U j) :=
  match plkIdx Mc m q with
  | none => 0
  | some r => (g.appLE _ _ (plk_le F Mc g hg (ind σ m) j)).hom (plkMinor F Mc (j PUnit.unit) σ m r)

end GlobalTheory.FlagPlucker

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure
section
noncomputable section

namespace GlobalTheory.LatHatClosed

open scoped TensorProduct RestrictedProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU Topology

variable (F : Type) [Field F] [NumberField F]

theorem isCompact_integralFinite :
    IsCompact {b : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), b.1 v ∈ v.adicCompletionIntegers F} := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

def intAd : AddSubgroup (AF F) where
  carrier := {a | evI F a = 0 ∧ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  zero_mem' := ⟨show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0 from map_zero _,
    fun v => by rw [map_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, fun v => ?_⟩
    · simp only [evI] at ha hb ⊢
      rw [show (a + b).1 = a.1 + b.1 from rfl, map_add (f := _), ha, hb, add_zero]
    · rw [map_add (evFin F v)]
      exact add_mem (ha' v) (hb' v)
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, fun v => ?_⟩
    · simp only [evI] at ha ⊢
      rw [show (-a).1 = -a.1 from rfl, map_neg, ha, neg_zero]
    · rw [map_neg]; exact neg_mem (ha' v)

theorem isCompact_intAd : IsCompact (intAd F : Set (AF F)) := by
  have e : (intAd F : Set (AF F)) = (({0} : Set (InfiniteAdeleRing F)) ×ˢ
      {b : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), b.1 v ∈ v.adicCompletionIntegers F} : Set _) := by
    ext a
    simp only [SetLike.mem_coe, Set.mem_prod, Set.mem_singleton_iff, Set.mem_setOf_eq]
    show (evI F a = 0 ∧ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ↔ _
    have h1 : evI F a = 0 ↔ a.1 = 0 := by
      simp only [evI]; exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff
    rw [h1]
    rfl
  rw [e]
  exact isCompact_singleton.prod (isCompact_integralFinite F)

theorem incV_add {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ} (x y : Fin n → E) :
    incV F (x + y) = incV F x + incV F y := by
  funext i; simp [incV, map_add (f := _)]

theorem incV_zero {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ} :
    incV F (0 : Fin n → E) = 0 := by
  funext i; simp [incV]

theorem incV_zsmul {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ} (m : ℤ) (x : Fin n → E) :
    incV F (m • x) = m • incV F x := by
  funext i; simp [incV, map_zsmul]

theorem isClosed_latHat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (X : Spc F E n), X.L.IsLattice E → IsClosed ((latHat X : AddSubgroup (Fin n → AE F E)) : Set (Fin n → AE F E)) := by
  intro F E _ _ _ _ _ n X hL
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  obtain ⟨s, hs⟩ := Submodule.FG.restrictScalars (R := ℤ) hL.fg
  let ψ : (s → AF F) →+ (Fin n → AE F E) :=
    { toFun := fun c => ∑ i, c i • incV F (i : Fin n → E)
      map_zero' := by simp
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib] }
  let P : AddSubgroup (s → AF F) := AddSubgroup.pi Set.univ (fun _ => intAd F)
  have hψc : Continuous ψ :=
    continuous_finsetSum _ fun i _ => by
      show Continuous fun c : s → AF F => c i • incV F (i : Fin n → E)
      exact (continuous_apply i : Continuous fun c : s → AF F => c i).smul
        (continuous_const : Continuous fun _ : s → AF F => incV F (i : Fin n → E))
  have hPc : IsCompact (P : Set (s → AF F)) := by
    have : (P : Set (s → AF F)) = Set.pi Set.univ (fun _ => (intAd F : Set (AF F))) := by
      ext c; simp [P, AddSubgroup.mem_pi]
    rw [this]; exact isCompact_univ_pi fun _ => isCompact_intAd F
  have hsL : ∀ i ∈ s, i ∈ X.L := fun i hi => by
    have : i ∈ Submodule.span ℤ (s : Set (Fin n → E)) := Submodule.subset_span hi
    rw [hs] at this; exact this
  have key : ∀ x ∈ Submodule.span ℤ (s : Set (Fin n → E)), ∀ a ∈ intAd F, a • incV F x ∈ P.map ψ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      intro a ha
      refine ⟨Pi.single ⟨y, hy⟩ a, ?_, ?_⟩
      · intro i _
        by_cases h : i = ⟨y, hy⟩
        · subst h; simpa using ha
        · simp [Pi.single_apply, h, zero_mem]
      · simp [ψ, Pi.single_apply, ite_smul]
    | zero =>
      intro a _
      rw [incV_zero, smul_zero]; exact zero_mem _
    | add y y' _ _ ih ih' =>
      intro a ha
      rw [incV_add, smul_add]; exact add_mem (ih a ha) (ih' a ha)
    | smul m y _ ih =>
      intro a ha
      rw [incV_zsmul, smul_comm, ← smul_assoc]
      exact ih (m • a) (zsmul_mem ha m)
  have heq : latHat X = P.map ψ := by
    apply le_antisymm
    · refine (AddSubgroup.closure_le _).2 ?_
      rintro z ⟨a, ha0, hav, x, hx, rfl⟩
      have hx' : x ∈ Submodule.span ℤ (s : Set (Fin n → E)) := by rw [hs]; exact hx
      exact key x hx' a ⟨ha0, hav⟩
    · rintro z ⟨c, hc, rfl⟩
      exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure
        ⟨c i, (hc i trivial).1, (hc i trivial).2, i, hsL i i.2, rfl⟩
  rw [heq, AddSubgroup.coe_map]
  exact (hPc.image hψc).isClosed

end GlobalTheory.LatHatClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjSelfReciprocalOfDvdEllipticPolynomial
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.SelfRecipFactor

theorem isSelfRecip_of_dvd_ell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]),
    P ∈ Ell E n → ∀ Q : E[X], Q.Monic → Irreducible Q → Q ∣ P →
      GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.IsSelfRecip E Q.natDegree Q := by
  intro E _ _ _ n P hP Q hQm hQi hQP
  obtain ⟨hPm, -, -, hroots⟩ := hP
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hP0 : P ≠ 0 := hPm.ne_zero
  have hnorm : ∀ z : ℂ, (Q.map τ).IsRoot z → ‖z‖ = 1 := by
    intro z hz
    apply hroots τ z
    rw [mem_roots (Polynomial.map_ne_zero hP0)]
    obtain ⟨R, rfl⟩ := hQP
    have hz' : eval z (Q.map τ) = 0 := hz
    simp [IsRoot, Polynomial.map_mul, eval_mul, hz']
  have hQ0 : Q.coeff 0 ≠ 0 := by
    intro h0
    have h : (Q.map τ).IsRoot 0 := by
      rw [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, h0, map_zero]
    have := hnorm 0 h
    simp at this
  set d := Q.natDegree with hd
  set c : E →+* E := (IsCMField.complexConj E : E →+* E) with hc
  have hτc : τ.comp c = (starRingEnd ℂ).comp τ := by
    ext x
    exact IsCMField.complexEmbedding_complexConj E τ x
  have hcQ0 : c (Q.coeff 0) ≠ 0 := by
    simpa using hQ0
  set S := GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.sharp E d Q with hS
  have hSdef : S = C (c (Q.coeff 0))⁻¹ * reflect d (Q.map c) := rfl
  have hdegc : (Q.map c).natDegree = d := natDegree_map c
  have hSm : S.Monic := by
    apply monic_of_natDegree_le_of_coeff_eq_one d
    · rw [hSdef]
      refine (natDegree_C_mul_le _ _).trans ?_
      refine natDegree_reflect_le.trans ?_
      rw [hdegc, max_self]
    · rw [hSdef, coeff_C_mul, coeff_reflect, revAt_le le_rfl, Nat.sub_self, coeff_map]
      exact inv_mul_cancel₀ hcQ0
  have hSdeg : S.natDegree ≤ d := by
    rw [hSdef]
    refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_reflect_le.trans ?_
    rw [hdegc, max_self]

  have hdeg : 0 < (Q.map τ).degree := by
    rw [degree_map]; exact degree_pos_of_irreducible hQi
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  have hz1 : ‖z‖ = 1 := hnorm z hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz1; simp at hz1
  have hzinv : z⁻¹ = (starRingEnd ℂ) z := Complex.inv_eq_conj hz1
  have hQz : eval₂ τ z Q = 0 := by
    have : eval z (Q.map τ) = 0 := hz
    rwa [eval_map] at this
  have hSz : eval₂ τ z S = 0 := by
    letI : Invertible (z⁻¹) := invertibleOfNonzero (inv_ne_zero hz0)
    have key := eval₂_reflect_mul_pow τ (z⁻¹) d (Q.map c) hdegc.le
    rw [invOf_eq_inv, inv_inv, eval₂_map, hτc, hzinv, ← Polynomial.hom_eval₂, hQz, map_zero] at key
    have hr : eval₂ τ z (reflect d (Q.map c)) = 0 := by
      rcases mul_eq_zero.1 key with h | h
      · exact h
      · exact absurd h (pow_ne_zero _ ((_root_.map_ne_zero _).2 hz0))
    rw [hSdef, eval₂_mul, hr, mul_zero]
  have hdvd : Q ∣ S := by
    by_contra h
    obtain ⟨a, b, hab⟩ := (hQi.coprime_iff_not_dvd).2 h
    have := congrArg (eval₂ τ z) hab
    rw [eval₂_add, eval₂_mul, eval₂_mul, hQz, hSz, eval₂_one] at this
    simp at this
  refine ⟨hQm, hQi, rfl, hQ0, ?_⟩
  exact (eq_of_monic_of_dvd_of_natDegree_le hQm hSm hdvd hSdeg).symm

end GlobalTheory.SelfRecipFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbTorsionAnyBase

open ReciprocityTheory.ChartRestriction.G.Out

theorem isFinite_and_flat_mulA (S : Scheme.{0}) (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (k : ℕ) (hk : 1 ≤ k) : IsFinite (mulA A k).left ∧ Flat (mulA A k).left := by
  have hc := hA.comm
  have hsm := hA.smooth
  have hpr := hA.proper
  have hm := GlobalTheory.AbLaw.MulN.isMonHom_mulA A k
  have hg : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IsFinite ((Over.pullback t).map (mulA A k)).left := fun K _ _ t => by
    rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA]
    exact GlobalTheory.MulFiniteAny.isFinite_mulA K _ (TLinPf.isAb_pullback t A hA) k hk
  have h1 : IsProper ((mulA A k).left ≫ A.hom) := by rw [Over.w]; exact hpr
  have h2 : IsProper (mulA A k).left := IsProper.of_comp _ A.hom
  have h3 : LocallyQuasiFinite (mulA A k).left :=
    LocallyQuasiFinite.of_finite_preimage_singleton _
      (GlobalTheory.MulFiniteFlat.finite_preimage_of_geomFibres _ hg)
  have hf : IsFinite (mulA A k).left := .of_isProper_of_locallyQuasiFinite _
  refine ⟨hf, GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S _ _ _
    inferInstance inferInstance inferInstance hf fun K _ _ t => ?_⟩
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    (TLinPf.isAb_pullback t A hA) _ inferInstance (hg K t)).1

theorem isFinite_and_flat_torsion : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B], IsAbelianScheme B → ∀ N : ℕ, 1 ≤ N → IsFinite (torsion B N).hom ∧ Flat (torsion B N).hom := by
  intro S B _ hB N hN
  obtain ⟨h1, h2⟩ := isFinite_and_flat_mulA S B hB N hN
  rw [Out.mulA, ← GrpTangent.mulN_eq_pow] at h1 h2
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) (GrpTangent.isPullback_torsion B N) h1,
    MorphismProperty.of_isPullback (P := @Flat) (GrpTangent.isPullback_torsion B N) h2⟩

end GlobalTheory.AbTorsionAnyBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.WeilSchrodinger

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsTransportF (σ : E →ₐ[F] E) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    (ψ : AddChar (AF F) ℂ) {ξ : AF F ⊗[F] E} {JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E}
    {κ : Type} [Fintype κ] (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ)
    (ω : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ))
    (om : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) →* Module.End ℂ ((κ → AF F) → ℂ)) : Prop :=
  ∀ (a : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA)) (b : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) (g : GAF σ JS) (h : GAF σ JT),
    mtF σ JT h = a.1.1 → mtF σ JS g = (b⁻¹).1.1ᵀ →
    ∀ Φ ∈ schA F κ, om (a, b) Φ ∈ schA F κ ∧ thetaTr F co ψ (om (a, b) Φ) = ω (g, h) (thetaTr F co ψ Φ)

end GlobalTheory.WeilSchrodinger

end
end

