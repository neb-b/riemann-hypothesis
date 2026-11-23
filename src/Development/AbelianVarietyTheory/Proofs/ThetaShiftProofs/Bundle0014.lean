module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsFibreIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToFSurjectiveFractionRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QkRelQkScaleEquiv

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsPullQk
section
noncomputable section

namespace GlobalTheory.ArcPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PsiEvenPull (proj)
open scoped CategoryTheory.Obj

open NumberField GlobalTheory.TorusExt

section Qk

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

def IsPullQk (hD : IsPullDeg φ D D') {k : ℕ} (p : QkPt D (FractionRing R) k) (p' : QkPt D' (FractionRing R') k) : Prop :=
  ∃ _ : Algebra (FractionRing R) (FractionRing R'), Compat φ (FractionRing R') ∧
    ∃ q : QkPt D (FractionRing R') k, QkExt (algebraMap (FractionRing R) (FractionRing R')) p q ∧
      p'.y = hD.xe.symm q.y ∧ IsPullGtF φ hD (FractionRing R') q.g p'.g

theorem IsPullQk.ext {hD : IsPullDeg φ D D'} {k : ℕ} {p : QkPt D (FractionRing R) k} {p' : QkPt D' (FractionRing R') k}
    (h : IsPullQk hD p p') {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
    (hF : Compat φ F) {q : QkPt D F k} {q' : QkPt D' F k} (hq : QkExt (algebraMap _ F) p q)
    (hq' : QkExt (algebraMap _ F) p' q') : q'.y = hD.xe.symm q.y ∧ IsPullGtF φ hD F q.g q'.g := by
  obtain ⟨_, hK, q₀, e₀, hy, hg⟩ := h
  have hc : (algebraMap (FractionRing R') F).comp (algebraMap (FractionRing R) (FractionRing R')) =
      algebraMap (FractionRing R) F := IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r =>
    (congrArg (algebraMap (FractionRing R') F) (hK r)).trans (hF r).symm)
  have hs : spMap (algebraMap (FractionRing R) F) =
      spMap (algebraMap (FractionRing R') F) ≫ spMap (algebraMap (FractionRing R) (FractionRing R')) := by
    rw [← hc, spMap_comp]
  have e₁ : QkExt (algebraMap (FractionRing R') F) q₀ q := by
    refine ⟨hq.1.trans e₀.1.symm, ?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · rw [hq.2.1, e₀.2.1, hs, Category.assoc]
    · refine (val_corr hJ (hq.2.2 χ) _).trans ((val_pull hJ _ _ _).trans (Eq.trans ?_
        ((val_pull hJ _ _ _).trans ((val_corr hJ (e₀.2.2 χ) _).trans (val_pull hJ _ _ _))).symm))
      exact congrArg (fun r => val (p.g.s χ) r y J) ((congrArg (𝟙 _ ≫ ·) hs).trans (Category.assoc _ _ _).symm)
  exact ⟨by rw [hq'.1, hy, e₁.1], isPullGtF_ext hD hF _ (RingHom.comp_id _) hg e₁ hq'⟩

theorem exists_isPullQk (hG : GlobalFnsSt) (hφ : Function.Injective φ) (hD : IsPullDeg φ D D') (hB : D.TauBimult)
    {k : ℕ} (p : QkPt D (FractionRing R) k) : ∃ p', IsPullQk hD p p' := by
  letI : Algebra (FractionRing R) (FractionRing R') := (fracMap hφ).toAlgebra
  have hK : Compat φ (FractionRing R') := fracMap_algebraMap hφ
  have hB' := TauPull.tauBimult_pull hG hD hB
  obtain ⟨q, hq, -⟩ := existsUnique_qkExt (F' := FractionRing R') hB (algebraMap (FractionRing R) (FractionRing R'))
    (RingHom.comp_id _) p
  exact ⟨pullQk hD hG hK hB hB' q, _, hK, q, hq, rfl, isPullGtF_pullGt hD hG hK _⟩

end Qk

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

def pullTate (hG : GlobalFnsSt) {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D₀ : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D₀ D') [Module (𝓞 E) D₀.X] [Module (𝓞 E) D'.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {oa' : letI := H.starRing; D'.OAct (𝓞 E)}
    (hx : ∀ (a : 𝓞 E) y, hD.xe (a • y) = a • hD.xe y)
    (ho : letI := H.starRing; ∀ a, (oa'.onB.act a).left ≫ proj hD = proj hD ≫ (oa.onB.act a).left)
    (hB : D₀.TauBimult) (hB' : D'.TauBimult) {F : Type} [Field F] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F] (hF : Compat φ F) (I : TateIsoQ D D₀ oa F) : TateIsoQ D D' oa' F :=
  letI := H.starRing
  { ζ := I.ζ
    ζ_prim := I.ζ_prim
    ζ_pow := I.ζ_pow
    ev := fun n a => pullQk hD hG hF hB hB' (I.ev n a)
    add := fun n hn a b => qkAdd_pullQk hD hG hF hB hB' (I.add n hn a b)
    lin := fun n hn x a => qkAct_pullQk hD hG hF hB hB' hx ho (I.lin n hn x a)
    ker := fun n hn a b => (equiv_pullQk hD hG hF hB hB' _ _).trans (I.ker n hn a b)
    onto := fun n hn p' => by
      obtain ⟨p, rfl⟩ := pullQk_surjective hD hG hF hB hB' p'
      obtain ⟨a, ha⟩ := I.onto n hn p
      exact ⟨a, (equiv_pullQk hD hG hF hB hB' _ _).2 ha⟩
    tower := fun n m hn hm a => by
      obtain ⟨q, h₁, h₂, h₃⟩ := I.tower n m hn hm a
      exact ⟨pullQk hD hG hF hB hB' q, congrArg hD.xe.symm h₁, isNsmul_pullGt hD hG hF h₂,
        (equiv_pullQk hD hG hF hB hB' _ _).2 h₃⟩
    isom := fun n hn a b => weilQkIs_pull hD hF rfl (isPullGtF_pullGt hD hG hF _) rfl (isPullGtF_pullGt hD hG hF _)
      (I.isom n hn a b) }

variable {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' O'' : Type} [CommRing O'] [IsDomain O']
  [CommRing O''] [IsDomain O''] {b : O →+* O'}

structure IsBC (f : O' →+* O'') (a : ArcIn D l β O' b) (a' : ArcIn D l β O'' (f.comp b))
    (hD : IsPullDeg f a.D₀ a'.D₀) : Prop where
  xe_smul : ∀ (x : 𝓞 E) (y : a'.D₀.X), hD.xe (x • y) = x • hD.xe y
  be_eq : ∀ y z : a'.D₀.X, a'.be y z = a.be (hD.xe y) (hD.xe z)
  act : letI := H.starRing
    ∀ x : 𝓞 E, (a'.oa.onB.act x).left ≫ hD.e.hom.left ≫ pullback.fst a.D₀.P.A.hom (specOf f) =
      (hD.e.hom.left ≫ pullback.fst a.D₀.P.A.hom (specOf f)) ≫ (a.oa.onB.act x).left
  eta : ∀ v, IsPullQk hD (a.eta v) (a'.eta v)
  etaA : ∀ v, IsPullQk hD (a.etaA v) (a'.etaA v)

def IsBC.xeL {f : O' →+* O''} {a : ArcIn D l β O' b} {a' : ArcIn D l β O'' (f.comp b)} {hD : IsPullDeg f a.D₀ a'.D₀}
    (h : IsBC f a a' hD) : a'.D₀.X ≃ₗ[𝓞 E] a.D₀.X := { hD.xe with map_smul' := h.xe_smul }

variable (hG : GlobalFnsSt) {f : O' →+* O''} (hf : Function.Injective f) (a : ArcIn D l β O' b) {D' : DegPre O''}
  (hD : IsPullDeg f a.D₀ D')

@[reducible] def pullModule : Module (𝓞 E) D'.X := hD.xe.module (𝓞 E)

theorem pullModule_smul (x : 𝓞 E) (y : D'.X) : letI := pullModule a hD; hD.xe (x • y) = x • hD.xe y :=
  hD.xe.apply_symm_apply _

def pullArc : ArcIn D l β O'' (f.comp b) :=
  letI := H.starRing
  letI := pullModule a hD
  have hx := pullModule_smul a hD
  have hB' := TauPull.tauBimult_pull hG hD a.bimult
  have ho := (exists_oAct hD hG hf a.oa hx).choose_spec
  { D₀ := D'
    mod := pullModule a hD
    oa := (exists_oAct hD hG hf a.oa hx).choose
    nontriv := have := a.nontriv; hD.xe.toEquiv.nontrivial
    even := PsiEvenPull.psiEven_pull hG _ _ f _ _ hD a.even
    bimult := hB'
    gen := fun y => psiUnitOn_pull hD hf y (a.gen _)
    w0 := traceFormTwistIso_of_pullback hD hf hx ho a.w0
    be := a.be.comp hD.xe.toAddMonoidHom.toIntLinearMap hD.xe.toAddMonoidHom.toIntLinearMap
    be_symm := fun y z => a.be_symm (hD.xe y) (hD.xe z)
    be_pos := fun y hy => a.be_pos (hD.xe y) (hD.xe.map_ne_zero_iff.2 hy)
    be_adj := fun x y z => by
      show a.be (hD.xe (x • y)) (hD.xe z) = a.be (hD.xe y) (hD.xe (H.bar x • z))
      rw [hx, hx, a.be_adj]
    be_dvd := fun y z => a.be_dvd (hD.xe y) (hD.xe z)
    eta := fun v => (exists_isPullQk hG hf hD a.bimult (a.eta v)).choose
    etaA := fun v => (exists_isPullQk hG hf hD a.bimult (a.etaA v)).choose
    geom := fun F _ _ _ r z hr hz f' hf' => by
      letI : Algebra (FractionRing O') F := ((algebraMap (FractionRing O'') F).comp (fracMap hf)).toAlgebra
      have hF : Compat f F := fun x => congrArg (algebraMap (FractionRing O'') F) (fracMap_algebraMap hf x)
      obtain ⟨h₁, I, h₂, h₃, h₄⟩ := a.geom F r z hr hz (f'.comp f) (RingHom.ext fun x => by
        rw [hf']; exact (hF x).symm)
      have lev : ∀ {k : ℕ} (p : QkPt a.D₀ (FractionRing O') k) (p' : QkPt D' (FractionRing O'') k) (e : QkPt a.D₀ F k),
          IsPullQk hD p p' → (∀ q, QkExt (algebraMap _ F) p q → QkPt.Equiv a.D₀ F q e) →
          ∀ q', QkExt (algebraMap _ F) p' q' → QkPt.Equiv D' F q' (pullQk hD hG hF a.bimult hB' e) := by
        intro k p p' e hp he q' hq'
        obtain ⟨q, hq, -⟩ := existsUnique_qkExt (F' := F) a.bimult (algebraMap (FractionRing O') F) (RingHom.comp_id _) p
        rw [(eq_pullQk_iff hD hG hF a.bimult hB' q q').2 (hp.ext hF hq hq'), equiv_pullQk]
        exact he q hq
      refine ⟨fun τ => ?_, pullTate hG hD hx ho a.bimult hB' hF I, h₂,
        fun v => lev _ _ _ (exists_isPullQk hG hf hD a.bimult (a.etaA v)).choose_spec (h₃ v),
        fun v hv => lev _ _ _ (exists_isPullQk hG hf hD a.bimult (a.eta v)).choose_spec (h₄ v hv)⟩
      obtain ⟨n, hn, hn'⟩ := h₁ τ
      refine ⟨n, (LiePull.lieMult_pull _ _ _ _ _ _ _ (ofRingAct a.oa.onB.toRingAct) _ (pull_grp hD) ho F _ τ n).2 ?_, ?_⟩
      · rw [← spMap_comp]; exact hn
      · rw [(({ hD.xe with map_smul' := hx } : D'.X ≃ₗ[𝓞 E] a.D₀.X)).finrank_eq]
        exact hn' }

theorem isBC_pullArc : IsBC f a (pullArc hG hf a hD) hD :=
  letI := H.starRing
  letI := pullModule a hD
  { xe_smul := pullModule_smul a hD
    be_eq := fun _ _ => rfl
    act := (exists_oAct hD hG hf a.oa (pullModule_smul a hD)).choose_spec
    eta := fun v => (exists_isPullQk hG hf hD a.bimult (a.eta v)).choose_spec
    etaA := fun v => (exists_isPullQk hG hf hD a.bimult (a.etaA v)).choose_spec }

theorem exists_isBC (hP : PolBaseChangeSt) (hG : GlobalFnsSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' O'' : Type}
    [CommRing O'] [IsDomain O'] [CommRing O''] [IsDomain O''] {b : O →+* O'} (a : ArcIn D l β O' b) (f : O' →+* O'')
    (hf : Function.Injective f) :
    ∃ (a' : ArcIn D l β O'' (f.comp b)) (hD : IsPullDeg f a.D₀ a'.D₀), IsBC f a a' hD ∧ a'.D₀.P.g = a.D₀.P.g := by
  obtain ⟨D', hD, -, hg⟩ := DegPull.exists_isPullDeg hP O' O'' f a.D₀ ⊤ (nonempty_psiOn_top _ a.gen) trivial
  exact ⟨pullArc hG hf a hD, hD, isBC_pullArc hG hf a hD, hg⟩

end GlobalTheory.ArcPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPtsEquiv
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LevelRatio

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem expandsG_smul {σ : H0 U.LG.L k} {f : ∀ x, SecBMod D.toPre k x} {s : Fam D.toPre F k} {e : F}
    (h : ∀ n, U.ExpandsAt n k σ f) (hs : ∀ x, famComp D.toPre F k x s = e • resF D.toPre F k x (f x)) :
    U.ExpandsG F k (e • extendSec U F k (genericSec U k σ) : GroupSec U F k) s := by
  refine (expandsG_iff U F k _ s).2 ⟨1, fun _ => e, fun _ => (σ, f), fun _ => h, by rw [Fin.sum_univ_one],
    fun α => ?_⟩
  rw [Fin.sum_univ_one]
  refine (hs α).trans (congrArg (fun q : SecFMod D.toPre F k α => e • q) (sec_ext' D.toPre.P.isLB fun y J hJ => ?_))
  exact (sval_resF D.toPre F _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
    (congrArg (fun q => sval (f α) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
      (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing R) F))))))).symm

theorem exists_expandsF (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R))))
    (hw : w.IsGen) : ∃ nu : (TFK (R := R) F ⟶ A.A) → A.L.ι → U.LG.L.ι → F,
      ∀ (σ : H0 U.LG.L k) (f : ∀ x, SecBMod D.toPre k x) (s : Fam D.toPre F k) (e : F),
        (∀ n, U.ExpandsAt n k σ f) → (∀ x, famComp D.toPre F k x s = e • resF D.toPre F k x (f x)) →
        ∃ t, U.ExpandsF F k w t s ∧ ∀ (z : TFK (R := R) F ⟶ A.A) (zG : Sp F ⟶ G.left) (i : A.L.ι) (j : U.LG.L.ι),
          z.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = zG → ⊤ ≤ z.left ⁻¹ᵁ A.L.U i →
          ⊤ ≤ zG ⁻¹ᵁ U.LG.L.U j → e * FormalValue.secVal (S := F) U σ zG j =
            nu z i j * valF (F := F) (ptSecT A.A z).left _ (t.f (fun _ => i)) := by
  let y : Sp F := IsLocalRing.closedPoint F
  refine ⟨fun z i j => valF (F := F) (z ≫ U.gen.inv).left ((U.LG.L.pull (pullback.fst G.hom (jK R))).U (fun _ => j) ⊓
    (A.L.pull U.gen.hom.left).U (fun _ => i)) (w.s (fun _ => j, fun _ => i)).val ^ k, fun σ f s e h hs => ?_⟩
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have hn' : U.genF F ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  obtain ⟨t, ht⟩ := ((isoRelM_bijective (k := k) (m := (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left)
    (g₁ := (snd (TFK (R := R) F) A.A).left) (h₁ := (U.genF F).left) A.isLB U.LG.isLB hw
    (congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')).2
      (e • extendSec U F k (genericSec U k σ) : GroupSec U F k)).exists
  refine ⟨t, ⟨_, ht, expandsG_smul U F h hs⟩, ?_⟩
  rintro z _ i j rfl hi hj
  let r : TFK (R := R) F ⟶ UnifPre.GF (G := G) F := lift (𝟙 _) (z ≫ U.gen.inv)
  have r₁ : r.left ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = (z ≫ U.gen.inv).left :=
    congrArg (fun q => q.left) (lift_snd _ _ : r ≫ snd _ _ = _)
  have r₂ : r.left ≫ (U.genF F).left = (ptSecT A.A z).left := by
    refine congrArg (fun q => q.left) (?_ : r ≫ U.genF F = ptSecT A.A z)
    apply CartesianMonoidalCategory.hom_ext <;> simp [r, ptSecT]
  have r₃ : r.left ≫ groupBase G F = 𝟙 _ := congrArg (fun q => q.left) (lift_fst _ _ : r ≫ fst _ _ = _)
  have r₄ : r.left ≫ UnifPre.gFK (G := G) F = z.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) := by
    rw [← Category.assoc, r₁, Over.comp_left, Category.assoc]
  have r₅ : r.left ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left = z.left := by
    rw [← Category.assoc, r₁, ← Over.comp_left, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have a₂ : (r.left ≫ UnifPre.gFK (G := G) F) y ∈ U.LG.L.U j := r₄.symm ▸ hj trivial
  have a₁ : (r.left ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left) y ∈ A.L.U i :=
    r₅.symm ▸ hi trivial
  have key := (isoRelM_iff w _ k _ ht.1 _ ht.2.1 _ _).1 ht _ r.left y j i a₂ a₁
  rw [Category.comp_id, r₁, r₂, powVal_smul (π := groupBase G F) (g := UnifPre.gFK (G := G) F) e _ r.left y a₂,
    r₃] at key
  refine (toStk y).injective ?_
  have m₀ : (z ≫ U.gen.inv).left y ∈ (U.LG.L.pull (pullback.fst G.hom (jK R))).U (fun _ => j) ⊓
      (A.L.pull U.gen.hom.left).U (fun _ => i) := by
    rw [← r₁]; exact ⟨mem_pull.2 a₂, mem_pull.2 a₁⟩
  rw [zpow_natCast, Units.val_pow_eq_pow_val] at key
  rw [map_mul, map_mul, map_pow, toStk_valF (F := F) _ _ y m₀ (w.s (fun _ => j, fun _ => i))]
  have m₁ : (ptSecT A.A z).left y ∈ (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U (fun _ => i) := by
    refine mem_wchart.2 fun _ => ?_
    have : (ptSecT A.A z).left ≫ (snd (TFK (R := R) F) A.A).left = z.left :=
      congrArg (fun q => q.left) (lift_snd _ _ : ptSecT A.A z ≫ snd _ _ = _)
    have h' : ((ptSecT A.A z).left ≫ (snd (TFK (R := R) F) A.A).left) y ∈ A.L.U i := this.symm ▸ hi trivial
    exact h'
  refine Eq.trans ?_ (key.trans (congrArg _ (ThetaScalar.toStk_valF_gs _ _ y m₁ _).symm))
  refine congrArg₂ (· * ·) (toStk_eq y e) ?_
  refine (FormalValue.toStkA_valR_eq_gs _ _ y (FormalValue.top_le_secChart hj) _).trans ?_
  rw [← r₄]
  exact ((gs_pullFn _ _ _ _ y (mem_wchart.2 fun _ => a₂)).trans ((gs_pullFn _ _ _ _ y (mem_wchart.2 fun _ => a₂)).trans
    (by rw [Category.assoc]; rfl))).symm

theorem exists_ptsEquiv : ∃ Φ : (TFK (R := R) F ⟶ A.A) ≃* (TF (R := R) F ⟶ G),
    ∀ z, (Φ z).left = z.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  have := U.gen_hom
  let e₁ := Hom.mulEquivCongrRight U.gen (TFK (R := R) F)
  let e₂ : (TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) ≃* (TF (R := R) F ⟶ G) :=
    TorsionLift.ptsEquiv (jK R) G (TFK (R := R) F) (jFK (R := R) F ≫ jK R) rfl
  have h₁ : ∀ z, e₁.symm z = z ≫ U.gen.inv := fun z => e₁.symm_apply_eq.2 (by
    show z = (z ≫ U.gen.inv) ≫ U.gen.hom
    simp)
  refine ⟨e₁.symm.trans e₂, fun z => ?_⟩
  rw [MulEquiv.trans_apply, h₁, ← Category.assoc, ← Over.comp_left]
  exact TorsionLift.ptsEquiv_left (jK R) G (TFK (R := R) F) (jFK (R := R) F ≫ jK R) rfl _

end GlobalTheory.LevelRatio

namespace GlobalTheory.LevelRatio

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem cross_secVal (hG : GlobalFnsSt) (hK : KerPowSt) (hk : 1 ≤ k) (p : QkPt D.toPre F k)
    (x : TFK (R := R) F ⟶ A.A) (xG : TF (R := R) F ⟶ G) (hx : QkToAkU U.toUnifPre F k p x)
    (hxG : x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = xG.left) : xG ^ k = 1 ∧
    ∀ (v : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))), v.IsGen →
      ∀ (σ₁ σ₂ σ₁' σ₂' : H0 U.LG.L k) (f₁ f₂ f₁' f₂' : ∀ x, SecBMod D.toPre k x) (s₁ s₂ s₁' s₂' : Fam D.toPre F k)
        (e₁ e₂ e₁' e₂' : F), (∀ n, U.toUnifPre.ExpandsAt n k σ₁ f₁) → (∀ n, U.toUnifPre.ExpandsAt n k σ₂ f₂) →
        (∀ n, U.toUnifPre.ExpandsAt n k σ₁' f₁') → (∀ n, U.toUnifPre.ExpandsAt n k σ₂' f₂') →
        (∀ x, famComp D.toPre F k x s₁ = e₁ • resF D.toPre F k x (f₁ x)) →
        (∀ x, famComp D.toPre F k x s₂ = e₂ • resF D.toPre F k x (f₂ x)) →
        (∀ x, famComp D.toPre F k x s₁' = e₁' • resF D.toPre F k x (f₁' x)) →
        (∀ x, famComp D.toPre F k x s₂' = e₂' • resF D.toPre F k x (f₂' x)) →
        PhiRel D.toPre F k p v s₁ s₁' → PhiRel D.toPre F k p v s₂ s₂' →
        ∀ (z : TF (R := R) F ⟶ G) (j j' : U.LG.L.ι), ⊤ ≤ (z * xG).left ⁻¹ᵁ U.LG.L.U j → ⊤ ≤ z.left ⁻¹ᵁ U.LG.L.U j' →
          e₁ * FormalValue.secVal (S := F) U.toUnifPre σ₁ (z * xG).left j *
              (e₂' * FormalValue.secVal (S := F) U.toUnifPre σ₂' z.left j') =
            e₂ * FormalValue.secVal (S := F) U.toUnifPre σ₂ (z * xG).left j *
              (e₁' * FormalValue.secVal (S := F) U.toUnifPre σ₁' z.left j') := by
  obtain ⟨w, hw⟩ := U.ext
  obtain ⟨Φ, hΦ⟩ := exists_ptsEquiv U.toUnifPre F
  obtain rfl : Φ x = xG := Over.OverMorphism.ext ((hΦ x).trans hxG)
  refine ⟨by rw [← map_pow, (hx w hw).1, map_one], fun v hv σ₁ σ₂ σ₁' σ₂' f₁ f₂ f₁' f₂' s₁ s₂ s₁' s₂' e₁ e₂ e₁' e₂'
    a₁ a₂ a₁' a₂' b₁ b₂ b₁' b₂' c₁ c₂ z j j' hj hj' => ?_⟩
  obtain ⟨z, rfl⟩ := Φ.surjective z
  rw [← map_mul] at hj ⊢
  obtain ⟨nu, hnu⟩ := exists_expandsF U.toUnifPre F (k := k) w hw
  obtain ⟨t₁, d₁, v₁⟩ := hnu σ₁ f₁ s₁ e₁ a₁ b₁
  obtain ⟨t₂, d₂, v₂⟩ := hnu σ₂ f₂ s₂ e₂ a₂ b₂
  obtain ⟨t₁', d₁', v₁'⟩ := hnu σ₁' f₁' s₁' e₁' a₁' b₁'
  obtain ⟨t₂', d₂', v₂'⟩ := hnu σ₂' f₂' s₂' e₂' a₂' b₂'
  let y : Sp F := IsLocalRing.closedPoint F
  have ch : ∀ u : TFK (R := R) F ⟶ A.A, ∃ i, ⊤ ≤ u.left ⁻¹ᵁ A.L.U i ∧
      ⊤ ≤ (ptSecT A.A u).left ⁻¹ᵁ (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U (fun _ => i) := fun u => by
    obtain ⟨i, hi⟩ := exists_chart A.isLB (u.left y)
    refine ⟨i, (top_le_iff_mem (F := F) u.left _ y).2 hi, (top_le_iff_mem (F := F) _ _ y).2 (mem_wchart.2 fun _ => ?_)⟩
    have : (ptSecT A.A u).left ≫ (snd (TFK (R := R) F) A.A).left = u.left :=
      congrArg (fun q => q.left) (lift_snd _ _ : ptSecT A.A u ≫ snd _ _ = _)
    have h' : ((ptSecT A.A u).left ≫ (snd (TFK (R := R) F) A.A).left) y ∈ A.L.U i := this.symm ▸ hi
    exact h'
  obtain ⟨i, hi, gi⟩ := ch (z * x)
  obtain ⟨i', hi', gi'⟩ := ch z
  have key := (values_at_translate hG hK U F hk p x hx w hw v hv).2.2 t₁ t₂ t₁' t₂' s₁ s₂ s₁' s₂' d₁ d₂ c₁ c₂ d₁' d₂'
    z _ _ gi gi'
  rw [v₁ _ _ i j (hΦ _).symm hi hj, v₂ _ _ i j (hΦ _).symm hi hj, v₁' _ _ i' j' (hΦ _).symm hi' hj',
    v₂' _ _ i' j' (hΦ _).symm hi' hj']
  linear_combination (nu (z * x) i j * nu z i' j') * key

end GlobalTheory.LevelRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PhiRelFamScale
section
noncomputable section

namespace GlobalTheory.TauTwist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusExt

section Sections

variable {X Y Z : Scheme.{0}} {L : LB X} {K K₁ K₂ K₃ : Type} [Fintype K] [Fintype K₁] [Fintype K₂] [Fintype K₃]

def scaleSec {M : LB Y} (c : Γ(Y, ⊤)ˣ) (s : LB.Sec M) : LB.Sec M where
  f j := (res (le_top : M.U j ≤ ⊤) c).val * s.f j
  compat i j := by
    have e : ∀ {W W' : Y.Opens} (h : W' ≤ W), (Y.presheaf.map (homOfLE h).op).hom (res (le_top : W ≤ ⊤) c).val =
        (res (le_top : W' ≤ ⊤) c).val := fun h => congrArg Units.val (res_res' _ _ c)
    rw [map_mul, map_mul, s.compat i j, e, e, mul_left_comm]

theorem sval_scaleSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : Γ(Y, ⊤)ˣ) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : sval (scaleSec c s) r z J = (gm r z ⊤ c).val * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ (hJ.mem φ r) _).trans
    (congrArg Units.val (gm_res r z le_top (hJ.mem φ r) c))) rfl)

variable {F : Type} [Field F]

def constUnit (p : Y ⟶ Sp F) (a : Fˣ) : Γ(Y, ⊤)ˣ := pullU p ⊤ (unitOn a)

theorem gm_constUnit (p : Y ⟶ Sp F) (a : Fˣ) (r : Z ⟶ Y) (z : Z) : gm r z ⊤ (constUnit p a) = unitAt (r ≫ p) z a :=
  gm_pull r p z ⊤ trivial (unitOn a)

theorem secRel_scale (hL : L.IsLB) (p : Y ⟶ Sp F) {h : Y ⟶ Y} (hp : h ≫ p = p) {e : Sp F ⟶ Y} (he : e ≫ p = 𝟙 _)
    {φ₁ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {φ₃ : K₃ → (Y ⟶ X)} {ε₃ : K₃ → ℤ}
    {φ : K → (Sp F ⟶ X)} {ε : K → ℤ} (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)) (s₂ : LB.Sec (LB.LinComb L φ₂ ε₂))
    {v v' : LB.Gen (LB.LinComb L φ ε)} {a b c : Fˣ} (habc : a = b * c)
    (hv : ∀ y J, Good L y J → val v' (𝟙 _) y J = unitAt (𝟙 _) y c * val v (𝟙 _) y J)
    (H : ∀ u : LB.Gen (LB.LinComb L φ₃ ε₃), u.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u e) v →
      GeneratorPullback.SecRel L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h φ₃ ε₃ u)
    (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen) (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u e) v') :
    GeneratorPullback.SecRel L φ₁ ε₁ (scaleSec (constUnit p a) s₁) φ₂ ε₂ (scaleSec (constUnit p b) s₂) h φ₃ ε₃ u := by
  have H₀ := (secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 (H (scaleGen (constUnit p c⁻¹) u) (scaleGen_isGen _ _ hu)
    (corr_of_val hL fun y J hJ => by
      have e₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ hc (𝟙 _)).trans (hv y J hJ))
      rw [val_pull hJ, val_scaleGen _ _ _ hJ, gm_constUnit, e₁, Category.assoc, he, Category.id_comp, map_inv,
        inv_mul_cancel_left]))
  refine (secRel_iff hL _ _ _ _ _ _ _ _ _ _).2 fun y J hJ => ?_
  rw [sval_scaleSec _ _ _ hJ, sval_scaleSec _ _ _ hJ, H₀ _ _ y J hJ, val_scaleGen _ _ _ hJ, gm_constUnit, gm_constUnit,
    gm_constUnit, Category.assoc, hp, habc, map_mul, map_inv, Units.val_mul, Units.val_mul]
  have := (unitAt (𝟙 Y ≫ p) y c).mul_inv
  linear_combination ((unitAt (𝟙 Y ≫ p) y b).val * sval s₂ (𝟙 Y ≫ h) y J * (val u (𝟙 Y) y J).val) * this

end Sections

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {ψ : PsiFam D} {hψ : ∀ χ, (ψ χ).IsGen}
  {F : Type} [Field F] [Algebra (FractionRing R) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.X] {w : O} {t : D.X → D.X → (FractionRing R)ˣ} {k : ℕ}
  {r : D.X → D.X → Fˣ}

def famScale (hw : w + star w = 1) (ht : IsScalarForm O t) (hq : PsiRel D ψ fun y => t y (w • y))
    (hr : IsRootForm O k t r) (hψ : ∀ χ, (ψ χ).IsGen) (s : Fam D F k) : Fam (withPsi D ψ hψ) F k where
  s α := scaleSec (constUnit (fst (TF (R := R) F) D.P.A).left (r α (w • α))) (s.s α)
  fe mu α := by
    refine secRel_scale D.P.isLB (fst (TF (R := R) F) D.P.A).left
      (congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trF D F mu ≫ _ = _))
      (congrArg (fun q => q.left) (lift_fst _ _ : DegPre.zF D F ≫ _ = _)) _ _
      (c := Units.map (algebraMap (FractionRing R) F).toMonoidHom (t mu α * t mu (w • mu) ^ k)) ?_
      (fun y J hJ => ?_) (s.fe mu α)
    · rw [hr.1.refine_add hw, map_mul, map_pow, ← hr.2, ← hr.2, smul_comm w k mu, hr.1.nsmul_left, hr.1.nsmul_right,
        hr.1.nsmul_right, hr.1.symm α mu]
      ac_rfl
    · have key : ∀ (y : (TF (R := R) F).left) J, Good D.P.L y J →
          val (DegPre.famMult (withPsi D ψ hψ) F k mu α) (𝟙 (TF (R := R) F) :).left y J =
          unitAt ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) y (t mu α * t mu (w • mu) ^ k) *
            val (DegPre.famMult D F k mu α) (𝟙 (TF (R := R) F) :).left y J := fun y J hJ => by
        rw [val_famMult (D := D) (𝟙 (TF (R := R) F)) hJ k mu α]
        refine (val_famMult (D := withPsi D ψ hψ) (𝟙 (TF (R := R) F)) hJ k mu α).trans ?_
        refine (congrArg₂ (· * ·) (hq.val_tau (ht.refine_add hw mu α) _ hJ) (congrArg₂ (· * ·)
          ((val_powGen _ _ _ _ _).trans (congrArg (· ^ k) (hq mu _ _ y J hJ))) rfl)).trans ?_
        rw [map_mul, map_pow, mul_pow, val_powGen (D.psi mu), _root_.mul_assoc (_ ^ k), _root_.mul_mul_mul_comm]
        rfl
      exact (key y J hJ).trans (congrArg₂ (· * ·) (unitAt_spMap _ (algebraMap (FractionRing R) F) y _) rfl)

variable (hw : w + star w = 1) (ht : IsScalarForm O t) (hq : PsiRel D ψ fun y => t y (w • y)) (hr : IsRootForm O k t r)

theorem phiRel_famScale (p : QkPt D F k)
    (v : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) {s s' : Fam D F k}
    (h : PhiRel D F k p v s s') :
    PhiRel (withPsi D ψ hψ) F k (qkScale hw ht hq hr hψ p) (scaleGen (unitOn (r p.y (w • p.y))) v)
      (famScale hw ht hq hr hψ s) (famScale hw ht hq hr hψ s') := fun α => by
  refine secRel_scale D.P.isLB (fst (TF (R := R) F) D.P.A).left
    (congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trPt D F p.g.b ≫ _ = _))
    (congrArg (fun q => q.left) (lift_fst _ _ : DegPre.zF D F ≫ _ = _)) _ _
    (c := r p.y α * r p.y (w • p.y)) ?_ (fun y J hJ => ?_) (h α)
  · show r (α + p.y) (w • (α + p.y)) = _
    rw [hr.1.refine_add hw, hr.1.symm α p.y]
    ac_rfl
  · refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_scale (r p.y α) (p.g.s α) _ hJ)
      (val_scale (r p.y (w • p.y)) v _ hJ)).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_mul hJ _ _ _).symm)))
    rw [map_mul, _root_.mul_mul_mul_comm]

include hw ht hq hr

theorem QkRel.weilQkIs_of {p q : QkPt D F k} {p' q' : QkPt (withPsi D ψ hψ) F k} (hp : QkRel r p p') (hq' : QkRel r q q')
    {ζ : F} (h : WeilQkIs (withPsi D ψ hψ) F k p' q' ζ) : WeilQkIs D F k p q ζ := by
  obtain rfl := (qkRel_qkScale hw ht hq hr p).unique hp
  obtain rfl := (qkRel_qkScale hw ht hq hr q).unique hq'
  intro v v' hv hv' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ α j
  have e := h _ _ (scaleGen_isGen _ _ hv) (scaleGen_isGen _ _ hv') _ _ _ _ _ (phiRel_famScale hw ht hq hr q v' h₁)
    (phiRel_famScale hw ht hq hr p v h₂) (phiRel_famScale hw ht hq hr p v h₃) (phiRel_famScale hw ht hq hr q v' h₄) α j
  exact (Units.mul_right_inj _).1 (e.trans (mul_left_comm _ _ _))

theorem QkRel.weilQkIs_iff {p q : QkPt D F k} {p' q' : QkPt (withPsi D ψ hψ) F k} (hp : QkRel r p p')
    (hq' : QkRel r q q') (ζ : F) : WeilQkIs (withPsi D ψ hψ) F k p' q' ζ ↔ WeilQkIs D F k p q ζ :=
  ⟨hp.weilQkIs_of hw ht hq hr hq',
    QkRel.weilQkIs_of (D := withPsi D ψ hψ) hw ht.inv hq.symm hr.inv hp.symm hq'.symm⟩

end GlobalTheory.TauTwist
end
end

