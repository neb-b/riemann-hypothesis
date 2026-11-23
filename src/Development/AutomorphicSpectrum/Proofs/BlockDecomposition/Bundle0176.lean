module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftEx
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LineLift

theorem liftEx : CrystallineSemistableComparison.E.LiftEx := by
  intro l _ H O _ X q κ C _ G D
  have key : ∀ p : ∀ T : C, Spec (CommRingCat.of (G.obj T).1.obj.U) ⟶ D.Y,
      (∀ T, p T ≫ D.f = (G.obj T).2.1) → ∃ Λ : Lift G D, Λ.p = p := by
    intro p hp
    have hh : ∀ {T T' : C} (φ : T ⟶ T'),
        (Spec.map (CommRingCat.ofHom (PAlg.mapU (G.map φ).1.hom)) ≫ p T) ≫ D.f = p T' ≫ D.f := by
      intro T T' φ
      rw [Category.assoc, hp, hp]
      exact congrArg Subtype.val (G.map φ).2
    have ex : ∀ {T T' : C} (φ : T ⟶ T'), ∃ w : ((G.obj T').1.obj.A)ˣ,
        (G.obj T').1.obj.sharp w = (Scheme.ΓSpecIso (CommRingCat.of (G.obj T').1.obj.U)).hom.hom
          (D.u (Spec.map (CommRingCat.ofHom (PAlg.mapU (G.map φ).1.hom)) ≫ p T) (p T') (hh φ)) := by
      intro T T' φ
      exact H.sharp _ (G.obj T').1.property (Units.map
        (Scheme.ΓSpecIso (CommRingCat.of (G.obj T').1.obj.U)).hom.hom.toMonoidHom
        (D.u (Spec.map (CommRingCat.ofHom (PAlg.mapU (G.map φ).1.hom)) ≫ p T) (p T') (hh φ)))
    exact ⟨{ p := p, hp := hp, w := fun φ => (ex φ).choose, hw := fun φ _ => (ex φ).choose_spec }, rfl⟩
  refine ⟨key, fun hE => ?_⟩
  have sec : ∀ T : C, ∃ p : Spec (CommRingCat.of (G.obj T).1.obj.U) ⟶ D.Y, p ≫ D.f = (G.obj T).2.1 := by
    intro T
    haveI := D.surj
    obtain ⟨s, hs⟩ := H.splitU _ (G.obj T).1.property (pullback D.f (G.obj T).2.1)
      (pullback.snd D.f (G.obj T).2.1) inferInstance inferInstance
    refine ⟨s ≫ pullback.fst D.f (G.obj T).2.1, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  choose p hp using sec
  obtain ⟨Λ, -⟩ := key p hp
  exact ⟨Λ⟩

end GlobalTheory.CompanionTheory.LineLift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineBC
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LineBase

theorem u_eq {X : Scheme.{0}} (D : LineData X) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y}
    (ha : a = a') (hb : b = b') (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) :
    D.u a b h = D.u a' b' h' := by
  subst ha hb
  rfl

noncomputable def pull {X' X : Scheme.{0}} (g : X' ⟶ X) (D : LineData X) : LineData X' where
  Y := pullback D.f g
  f := pullback.snd D.f g
  sm := by
    exact MorphismProperty.pullback_snd (P := @Smooth) D.f g D.sm
  surj := by
    exact MorphismProperty.pullback_snd (P := @Surjective) D.f g D.surj
  u := fun {V} a b h => D.u (a ≫ pullback.fst D.f g) (b ≫ pullback.fst D.f g) (by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc, h])
  nat := fun {V' V} k a b h => by
    rw [← D.nat k (a ≫ pullback.fst D.f g) (b ≫ pullback.fst D.f g)]
    exact u_eq D (Category.assoc _ _ _) (Category.assoc _ _ _) _ _
  coc := fun {V} a b c h h' => D.coc _ _ _ _ _

theorem lineBC : CrystallineSemistableComparison.E.LineBC := by
  intro X' X g D
  refine ⟨pull g D, pullback.fst D.f g, pullback.condition, ?_, ?_⟩
  · intro V a x h
    exact ⟨pullback.lift a x h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  · intro V a b h h'
    rfl

end GlobalTheory.CompanionTheory.LineBase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowDivPowSucc
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtReduction

section Abstract
universe w u v
variable {R R₁ R₂ R₃ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₃] {C : Type u} [Category.{v} C]

theorem pull_sq {F : C ⥤ ModuleCat.{w} R} {F₁ : C ⥤ ModuleCat.{w} R₁} {F₂ : C ⥤ ModuleCat.{w} R₂} {F₃ : C ⥤ ModuleCat.{w} R₃}
    {σ₁ : R →+* R₁} {σ₂ : R₁ →+* R₃} {σ₃ : R →+* R₂} {σ₄ : R₂ →+* R₃}
    (a : Mor F F₁ σ₁) (b : Mor F₁ F₃ σ₂) (c : Mor F F₂ σ₃) (e : Mor F₂ F₃ σ₄) (n : ℕ)
    (h : ∀ z, b.pullC n (a.pullC n z) = e.pullC n (c.pullC n z)) (x : CH.H F n) :
    b.pull n (a.pull n x) = e.pull n (c.pull n x) := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z))

end Abstract

variable {l : ℕ} [Fact l.Prime]

def lcCast {U : Type*} [TopologicalSpace U] {Q q : ℕ} (h : q ∣ Q) :
    LocallyConstant U (ZMod Q) →+ LocallyConstant U (ZMod q) where
  toFun f := f.map (ZMod.castHom h (ZMod q))
  map_zero' := by ext v; simp
  map_add' f g := by
    ext v
    exact map_add (ZMod.castHom h (ZMod q)) (f v) (g v)

theorem pow_div_pow_succ (n : ℕ) : l ^ (n + 1) / l ^ n = l := by
  have h : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  rw [pow_succ', Nat.mul_div_cancel _ h]

theorem rho_pow (r : Roots l) (n : ℕ) : (r.ρ n).1 = (r.ρ (n + 1)).1 ^ l := by
  apply (clToC l).injective
  rw [map_pow, r.hρ, r.hρ, rootSeq_succ_pow]

theorem lcRes_id {U : Scheme.{0}} (q : ℕ) (f : LocallyConstant U (ZMod q)) : lcRes q (𝟙 U) f = f := by
  ext v
  simp [lcRes]

theorem zeta_red (r : Roots l) (A : PAlg l) (n : ℕ) :
    (r.zeta A n).1 = (primRes (𝟙 (SU A)) (r.zeta A (n + 1))).1 ^ (l ^ (n + 1) / l ^ n) := by
  rw [pow_div_pow_succ]
  change ((toΓ A.Ug).comp (kb A)) (r.ρ n).1 = (𝟙 (SU A) : SU A ⟶ SU A).appTop.hom (((toΓ A.Ug).comp (kb A)) (r.ρ (n + 1)).1) ^ l
  rw [rho_pow r n, map_pow]
  simp

theorem lc_red (hN : LcNat) (H : RIn l) (A : Test l) (n : ℕ) (f : LocallyConstant (SU A.obj) (ZMod (l ^ (n + 1)))) :
    A.obj.red n.le_succ (lcA A.obj (n + 1) f) = lcA A.obj n (lcCast (pow_dvd_pow l n.le_succ) f) :=
  (hN l H _ A.property n).2 f

variable {C : Type 1} [Category.{0} C]

def redMor (H : RIn l) (r : Roots l) (G : C ⥤ Test l) (n : ℕ) :
    Mor (probe H r G (n + 1)).L (probe H r G n).L (RingHom.id ℤ) where
  G := 𝟭 C
  τ c :=
    { toFun := lcCast (pow_dvd_pow l n.le_succ)
      map_add' := map_add _
      map_smul' := fun z x => (map_zsmul (lcCast (U := (probe H r G n).U c) (pow_dvd_pow l n.le_succ)) z x).trans rfl }
  nat φ x := rfl

end GlobalTheory.CompanionTheory.EtReduction

namespace GlobalTheory.CompanionTheory.EtReduction

variable {l : ℕ} [Fact l.Prime]

theorem red_lc_sq (hN : LcNat) (H : RIn l) (r : Roots l) (P : PAlg l ⥤ Type) (n j : ℕ)
    (c : CH.H (probe H r (𝟭 (El P) ⋙ CategoryOfElements.π _) (n + 1)).L j) :
    (MSys P j).r n ((lcMor hN H r (𝟭 (El P) ⋙ CategoryOfElements.π _) (n + 1)).pull j c) =
      (lcMor hN H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n).pull j
        ((redMor H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n).pull j c) :=
  pull_sq (F := (probe H r (𝟭 (El P) ⋙ CategoryOfElements.π _) (n + 1)).L)
    (F₁ := CH.modF (AcrEl P (n + 1))) (F₂ := (probe H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n).L)
    (F₃ := CH.modF (AcrEl P n))
    (lcMor hN H r (𝟭 (El P) ⋙ CategoryOfElements.π _) (n + 1)) (Mor.ofNatTrans (redEl P n.le_succ))
    (redMor H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n) (lcMor hN H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n) j
    (fun z => funext fun s => lc_red hN H (s.obj (Fin.last j)).1 n (z s)) c

end GlobalTheory.CompanionTheory.EtReduction

namespace GlobalTheory.CompanionTheory.EtReduction

theorem fred_of_etRed : EtRed → FRed := by
  intro hE E hN l _ H r K M n j x
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have key := hE E.gen E.red E.op (l ^ (n + 1)) (l ^ n) (pow_dvd_pow l n.le_succ) (El M.P) (El M.P)
    (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) (n + 1)) (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n) (gb M)
    (pts H r M (𝟭 _) (n + 1)) (pts H r M (𝟭 _) n) (redMor H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n)
    (fun c => 𝟙 _) (fun φ => (Category.id_comp _).trans (Category.comp_id _).symm)
    (fun c f => (lcRes_id _ _).symm)
    (fun c => (Category.id_comp _).symm)
    (fun c => zeta_red r _ n) 0 j x
  exact (red_lc_sq hN H r M.P n j _).trans (congrArg _ key)

end GlobalTheory.CompanionTheory.EtReduction
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimResZetaX
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.FRootCls

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem rho_succ (r : Roots l) (n : ℕ) : (r.ρ n).1 = (r.ρ (n + 1)).1 ^ l := by
  apply (clToC l).injective
  rw [map_pow, r.hρ, r.hρ, rootSeq_succ_pow]

theorem pow_div_succ (n : ℕ) : l ^ (n + 1) / l ^ n = l := by
  have h : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  rw [pow_succ, Nat.mul_comm, Nat.mul_div_cancel _ h]

theorem zetaX_succ (r : Roots l) (M : Model l K) (n : ℕ) :
    (r.zetaX M n).1 = (r.zetaX M (n + 1)).1 ^ (l ^ (n + 1) / l ^ n) := by
  rw [pow_div_succ]
  change (pullback.snd _ _ : gb M ⟶ Spec (CommRingCat.of (PadicAlgCl l))).appTop.hom (toΓ _ (r.ρ n).1) =
    ((pullback.snd _ _ : gb M ⟶ Spec (CommRingCat.of (PadicAlgCl l))).appTop.hom (toΓ _ (r.ρ (n + 1)).1)) ^ l
  rw [rho_succ r n, map_pow, map_pow]

theorem primRes_zetaX (r : Roots l) (M : Model l K) (n : ℕ) (A : PAlg l) (y : M.P.obj A) :
    primRes (geomPt M A y) (r.zetaX M n) = r.zeta A n := by
  refine Subtype.ext ?_
  change (geomPt M A y).appTop.hom ((pullback.snd _ _ : gb M ⟶ Spec (CommRingCat.of (PadicAlgCl l))).appTop.hom (toΓ _ (r.ρ n).1)) =
    toΓ A.Ug (kb A (r.ρ n).1)
  rw [← toΓ_nat (kb A), ← geomPt_snd M A y, Scheme.Hom.comp_appTop]
  rfl

def lcRing (hL : LcSpec) (H : RIn l) (A : PAlg l) (hA : A.IsTest) (n : ℕ) : LocallyConstant (SU A) (ZMod (l ^ n)) →+* A.Acr n where
  toFun := lcA A n
  map_one' := (hL l H A hA n).2.1
  map_mul' := (hL l H A hA n).2.2.1
  map_zero' := map_zero _
  map_add' := map_add _

theorem lcMor_one (hL : LcSpec) (hM : MorCup) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    (lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).pull 0
      (oneH (lcF (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).S (l ^ n))) = oneH (AcrEl M.P n) :=
  (hM ℤ (Acris l) (Int.castRingHom (Acris l)) (El M.P) (lcF (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).S (l ^ n))
    (AcrEl M.P n) (lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n)
    (fun c => lcRing hL H c.1.obj c.1.property n) (fun _ _ => rfl)).1

def rootSys (hO : InOp) (hR : InRed) (hRR : RedRoot) (r : Roots l) (M : Model l K) (i : ℤ) : Hl l (sch.obj (gb M)) (0 : ℕ) i :=
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  ⟨fun n => rootClass i (r.zetaX M n), fun n =>
    hRR hO hR (l ^ (n + 1)) (l ^ n) (pow_dvd_pow l n.le_succ) i (gb M) (r.zetaX M (n + 1)) (r.zetaX M n) (zetaX_succ r M n)⟩

theorem etVal (hEt : EtRoot) (hg : InGen) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) (i : ℤ) [NeZero (l ^ n)] :
    (pts H r M (𝟭 _) n).et i 0 (rootClass i (r.zetaX M n)) =
      oneH (lcF (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).S (l ^ n)) :=
  hEt hg (l ^ n) (El M.P) (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n) (gb M) (pts H r M (𝟭 _) n)
    (r.zetaX M n) (fun c => primRes_zetaX r M n _ _) i

theorem eM_root (hL : LcSpec) (hM : MorCup) (hEt : EtRoot) (hg : InGen) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) (i : ℤ) [NeZero (l ^ n)] :
    eM hN H r M n i 0 (rootClass i (r.zetaX M n)) = oneH (AcrEl M.P n) := by
  refine Eq.trans (congrArg ((lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).pull 0) (etVal hEt hg hN H r M n i)) ?_
  exact lcMor_one hL hM hN H r M n

theorem eM_rootSys (hL : LcSpec) (hM : MorCup) (hEt : EtRoot) (hRR : RedRoot) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l)
    (M : Model l K) (i : ℤ) (n : ℕ) : eM hN H r M n i 0 ((rootSys E.op E.red hRR r M i).1 n) = oneH (AcrEl M.P n) :=
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  eM_root hL hM hEt E.gen hN H r M n i

theorem froot : CrystallineSemistableComparison.E.EtRoot → CrystallineSemistableComparison.E.RedRoot → CrystallineSemistableComparison.E.MorCup → CrystallineSemistableComparison.E.LcSpec → CrystallineSemistableComparison.E.FRoot :=
  fun hEt hRR hM hL E hN _ _ H r _ M i => ⟨rootSys E.op E.red hRR r M i, eM_rootSys hL hM hEt hRR E hN H r M i⟩

end GlobalTheory.CompanionTheory.FRootCls
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullPullOfPullC
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.FEquiProof

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem pull_pull_of_pullC {R₀ R₁ R₂ R₃ : Type} [CommRing R₀] [CommRing R₁] [CommRing R₂] [CommRing R₃]
    {C₀ C₁ C₂ C₃ : Type 1} [Category.{0} C₀] [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃]
    {F₀ : C₀ ⥤ ModuleCat.{0} R₀} {F₁ : C₁ ⥤ ModuleCat.{0} R₁} {F₂ : C₂ ⥤ ModuleCat.{0} R₂} {F₃ : C₃ ⥤ ModuleCat.{0} R₃}
    {a : R₀ →+* R₁} {b : R₁ →+* R₃} {c : R₀ →+* R₂} {e : R₂ →+* R₃}
    (m₁ : Mor F₀ F₁ a) (m₂ : Mor F₁ F₃ b) (m₃ : Mor F₀ F₂ c) (m₄ : Mor F₂ F₃ e) (j : ℕ)
    (h : ∀ z : Cn F₀ j, m₂.pullC j (m₁.pullC j z) = m₄.pullC j (m₃.pullC j z)) (x : H F₀ j) :
    m₂.pull j (m₁.pull j x) = m₄.pull j (m₃.pull j x) := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := ((cx F₃).B j).submoduleOf ((cx F₃).Z j))) (Subtype.ext (h z))

theorem twUg_sharp (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (e : (PAlg.tw σ A).A) :
    twUg σ A (algebraMap (PAlg.tw σ A).U (PAlg.tw σ A).Ug ((PAlg.tw σ A).sharp e)) =
      algebraMap A.U A.Ug (A.sharp (PAlg.twId σ A e)) := by
  rw [twUg_algebraMap]
  refine congrArg (algebraMap A.U A.Ug) ?_
  change PAlg.twU σ A ((PAlg.tw σ A).th (WittVector.teichmuller l e)) = A.th (WittVector.teichmuller l (PAlg.twId σ A e))
  rw [PAlg.twU_th, WittVector.map_teichmuller]

theorem twAcr_lcA (hN : LcNat) (H : RIn l) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (hA : A.IsTest) (n : ℕ)
    (f : LocallyConstant (SU (PAlg.tw σ A)) (ZMod (l ^ n))) :
    PAlg.twAcr σ A n (lcA (PAlg.tw σ A) n f) =
      lcA A n (lcRes (l ^ n) (Spec.map (CommRingCat.ofHom (twUg σ A))) f) :=
  (hN l H _ (hA.tw σ) n).1 A hA (PAlg.twId σ A) (PAlg.pdOk_twId σ A) (twUg σ A) (fun e _ => twUg_sharp σ A e) f

theorem lcRes_sq {q : ℕ} {A B C D : Scheme.{0}} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D} (e : a ≫ b = c ≫ d)
    (x : LocallyConstant D (ZMod q)) : lcRes q a (lcRes q b x) = lcRes q c (lcRes q d x) := by
  ext v
  have e' : b (a v) = d (c v) := by
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact congrArg x e'

abbrev pM (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) : Probe (El M.P) (l ^ n) :=
  probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

abbrev tM (M : Model l K) (σ : Gal(PadicAlgCl l/K)) : El M.P ⥤ El M.P :=
  elTw σ (pxTw M.p (okToOC l K) σ (galOC_okToOC σ))

def gM (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n : ℕ) (c : El M.P) :
    (pM H r M n).U c ⟶ (pM H r M n).U ((tM M σ).obj c) :=
  Spec.map (CommRingCat.ofHom (twUg σ c.1.obj))

theorem gM_sq (hT : TwUg) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n : ℕ) {c c' : El M.P}
    (φ : c ⟶ c') : gM H r M σ n c' ≫ ((pM H r M n).S.map ((tM M σ).map φ)).unop =
      ((pM H r M n).S.map φ).unop ≫ gM H r M σ n c := by
  change Spec.map (CommRingCat.ofHom (twUg σ c'.1.obj)) ≫
      Spec.map (CommRingCat.ofHom (PAlg.mapUg (PAlg.twMap σ φ.1.hom))) =
    Spec.map (CommRingCat.ofHom (PAlg.mapUg φ.1.hom)) ≫ Spec.map (CommRingCat.ofHom (twUg σ c.1.obj))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) ((hT l K σ).1 _ _ φ.1.hom)

def twMor (hT : TwUg) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n : ℕ) :
    Mor (pM H r M n).L (pM H r M n).L (RingHom.id ℤ) where
  G := tM M σ
  τ c := (lcRes (l ^ n) (gM H r M σ n c)).toAddMonoidHom.toIntLinearMap
  nat {c c'} φ x := by
    have e := gM_sq hT H r M σ n φ
    change lcRes (l ^ n) (gM H r M σ n c') (lcRes (l ^ n) ((pM H r M n).S.map ((tM M σ).map φ)).unop x) =
      lcRes (l ^ n) ((pM H r M n).S.map φ).unop (lcRes (l ^ n) (gM H r M σ n c) x)
    exact lcRes_sq e x

def lM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    Mor (pM H r M n).L (modF (AcrEl M.P n)) (Int.castRingHom (Acris l)) :=
  lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

abbrev gaM (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n : ℕ) : Mor (modF (AcrEl M.P n)) (modF (AcrEl M.P n)) (ACris.galCris σ) :=
  galMor σ (pxTw M.p (okToOC l K) σ (galOC_okToOC σ)) n

theorem lM_pullC_twMor (hT : TwUg) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ)
    (z : Cn (pM H r M n).L j) :
    (lM hN H r M n).pullC j ((twMor hT H r M σ n).pullC j z) = (gaM M σ n).pullC j ((lM hN H r M n).pullC j z) := by
  funext s
  have hA := (s.obj (Fin.last j)).1.property
  let f : LocallyConstant (SU (PAlg.tw σ (s.obj (Fin.last j)).1.obj)) (ZMod (l ^ n)) := z (s ⋙ tM M σ)
  exact (twAcr_lcA hN H σ (s.obj (Fin.last j)).1.obj hA n f).symm

theorem lM_pull_twMor (hT : TwUg) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ)
    (x : CH.H (pM H r M n).L j) :
    (lM hN H r M n).pull j ((twMor hT H r M σ n).pull j x) = (gaM M σ n).pull j ((lM hN H r M n).pull j x) :=
  pull_pull_of_pullC (twMor hT H r M σ n) (lM hN H r M n) (lM hN H r M n) (gaM M σ n) j
    (lM_pullC_twMor hT hN H r M σ n j) x

theorem key (hE : CrystallineSemistableComparison.E.EtNat) (hT : CrystallineSemistableComparison.E.TwUg) (E : EtIn) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ)
    (x : Ht (l ^ n) (sch.obj (gb M)) j 0) :
    (twMor hT H r M σ n).pull j ((pts H r M (𝟭 _) n).et 0 j x) =
      (pts H r M (𝟭 _) n).et 0 j (pull _ (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ)) _ j x) :=
  hE E.gen (l ^ n) (El M.P) (El M.P) (pM H r M n) (pM H r M n) (gb M) (gb M)
    (pts H r M (𝟭 _) n) (pts H r M (𝟭 _) n) (GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ) (twMor hT H r M σ n)
    (gM H r M σ n) (fun φ => gM_sq hT H r M σ n φ) (fun c f => rfl)
    (fun c => (hT l K σ).2.2 M c.1.obj c.2) 0 (Or.inl rfl) j x

theorem eM_apply (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n j : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) j 0) :
    eM hN H r M n 0 j x = (lM hN H r M n).pull j ((pts H r M (𝟭 _) n).et 0 j x) := rfl

theorem galMH_apply (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ) (y : M.MH n j) :
    M.galMH σ n j y = (gaM M σ n).pull j y := rfl

theorem equi_at (hE : CrystallineSemistableComparison.E.EtNat) (hT : CrystallineSemistableComparison.E.TwUg) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K)
    (σ : Gal(PadicAlgCl l/K)) (n j : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) j 0) :
    eM hN H r M n 0 j (pull _ (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ)) _ j x) = M.galMH σ n j (eM hN H r M n 0 j x) :=
  (eM_apply hN H r M n j _).trans ((congrArg ((lM hN H r M n).pull j) (key hE hT E H r M σ n j x).symm).trans
    ((lM_pull_twMor hT hN H r M σ n j _).trans ((congrArg ((gaM M σ n).pull j) (eM_apply hN H r M n j x).symm).trans
      (galMH_apply M σ n j _).symm)))

theorem fEqui : CrystallineSemistableComparison.E.EtNat → CrystallineSemistableComparison.E.TwUg → CrystallineSemistableComparison.E.FEqui :=
  fun hE hT E hN l _ H r K M n j σ x => equi_at hE hT E hN H r M σ n j x

end GlobalTheory.CompanionTheory.FEquiProof
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullSquare
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.FResProof

theorem pull_square {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] {σ : R₀ →+* R₁} {C₀ C₁ : Type 1}
    [Category.{0} C₀] [Category.{0} C₁] {F₀ : C₀ ⥤ ModuleCat.{0} R₀} {F₁ : C₀ ⥤ ModuleCat.{0} R₁}
    {F₀' : C₁ ⥤ ModuleCat.{0} R₀} {F₂ : C₁ ⥤ ModuleCat.{0} R₁} (m₁ : Mor F₀ F₁ σ) (e : Mor F₁ F₂ (RingHom.id R₁))
    (a : Mor F₀ F₀' (RingHom.id R₀)) (m₂ : Mor F₀' F₂ σ) (j : ℕ)
    (h : ∀ z : Cn F₀ j, e.pullC j (m₁.pullC j z) = m₂.pullC j (a.pullC j z)) (y : CH.H F₀ j) :
    e.pull j (m₁.pull j y) = m₂.pull j (a.pull j y) := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z))

theorem lcRes_id (q : ℕ) {U : Scheme.{0}} (f : LocallyConstant U (ZMod q)) : lcRes q (𝟙 U) f = f := by
  ext x; rfl

theorem primRes_id {q : ℕ} {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) : primRes (𝟙 U) ζ = ζ :=
  Subtype.ext (by
    change (𝟙 U : U ⟶ U).appTop.hom ζ.1 = ζ.1
    simp)

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def mG (H : RIn l) (r : Roots l) (M : Model l K) {C : Type 1} [Category.{0} C] (G : C ⥤ El M.P) (n : ℕ) :
    Mor (probe H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n).L (probe H r (G ⋙ CategoryOfElements.π _) n).L
      (RingHom.id ℤ) where
  G := G
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem square (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) {C : Type 1} [Category.{0} C] (G : C ⥤ El M.P)
    (n j : ℕ) (y : CH.H (probe H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n).L j) :
    (Mor.restrict (modF (AcrEl M.P n)) G).pull j ((lcMor hN H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n).pull j y) =
      (lcMor hN H r (G ⋙ CategoryOfElements.π _) n).pull j ((mG H r M G n).pull j y) :=
  pull_square (lcMor hN H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n) (Mor.restrict (modF (AcrEl M.P n)) G)
    (mG H r M G n) (lcMor hN H r (G ⋙ CategoryOfElements.π _) n) j (fun z => rfl) y

theorem pull_sch_id (q : ℕ) (i : ℤ) (j : ℕ) (X : Scheme.{0}) (x : Ht q (sch.obj X) j i) :
    pull _ (sch.map (𝟙 X)) _ j x = x := by
  rw [CategoryTheory.Functor.map_id, GlobalTheory.EtC.pull_id]


set_option maxHeartbeats 1000000 in
theorem et_restrict (hE : EtNat) (hg : InGen) (H : RIn l) (r : Roots l) (M : Model l K) {C : Type 1} [Category.{0} C]
    (G : C ⥤ El M.P) (n : ℕ) (i : ℤ) (j : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) j i) :
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    (mG H r M G n).pull j ((pts H r M (𝟭 _) n).et i j x) = (pts H r M G n).et i j x := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine (hE hg (l ^ n) (El M.P) C (probe H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n)
    (probe H r (G ⋙ CategoryOfElements.π _) n) (gb M) (gb M) (pts H r M (𝟭 _) n) (pts H r M G n) (𝟙 _)
    (mG H r M G n) (fun c => 𝟙 _) (fun φ => ?_)
    (fun c f => (lcRes_id _ f).symm) (fun c => ?_) i
    (Or.inr fun c => primRes_id _) j x).trans (congrArg _ (pull_sch_id _ _ _ _ x))
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

end GlobalTheory.CompanionTheory.FResProof

theorem GlobalTheory.CompanionTheory.FResProof.fRes : CrystallineSemistableComparison.E.EtNat → CrystallineSemistableComparison.E.FRes := by
  intro hE E hN l _ H r K M C _ G n i j x
  exact (GlobalTheory.CompanionTheory.FResProof.square hN H r M G n j _).trans
    (congrArg _ (GlobalTheory.CompanionTheory.FResProof.et_restrict hE E.gen H r M G n i j x))
end
end

