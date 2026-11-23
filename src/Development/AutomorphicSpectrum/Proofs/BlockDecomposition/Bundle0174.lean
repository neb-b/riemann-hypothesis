module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0164
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0157
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0170
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRoot
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.FKum

variable {l : ℕ} [Fact l.Prime]

def tu (A : PAlg l) : A.A →* Γ(SU A, ⊤) :=
  ((toΓ A.Ug).toMonoidHom.comp (algebraMap A.U A.Ug).toMonoidHom).comp A.sharp

theorem tu_apply (A : PAlg l) (a : A.A) : tu A a = toΓ A.Ug (algebraMap A.U A.Ug (A.sharp a)) := rfl

theorem sharp_nat {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    PAlg.mapU f (A.sharp a) = B.sharp (PAlg.Hom.f f a) := by
  change PAlg.mapU f (A.th (WittVector.teichmuller l a)) = B.th (WittVector.teichmuller l (PAlg.Hom.f f a))
  rw [PAlg.mapU_th]
  exact congrArg B.th (WittVector.map_teichmuller _ _ _)

theorem tu_nat {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    (Spec.map (CommRingCat.ofHom (PAlg.mapUg f))).appTop.hom (tu A a) = tu B (PAlg.Hom.f f a) := by
  rw [tu_apply, toΓ_nat, PAlg.mapUg_algebraMap, sharp_nat]; rfl

theorem u_congr {X : Scheme.{0}} (D : LineData X) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y} (ha : a = a') (hb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : D.u a b h = D.u a' b' h' := by
  subst ha hb; rfl

theorem toΓ_hom (B : Type) [CommRing B] (x : Γ(Spec (CommRingCat.of B), ⊤)) :
    toΓ B ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom x) = x :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of B)).hom_inv_id x

abbrev gU (B : PAlg l) : SU B ⟶ Spec (CommRingCat.of B.U) := Spec.map (CommRingCat.ofHom (algebraMap B.U B.Ug))

theorem tu_of_sharp {X : Scheme.{0}} (D : LineData X) (B : PAlg l) (a b : Spec (CommRingCat.of B.U) ⟶ D.Y)
    (h : a ≫ D.f = b ≫ D.f) (w : B.A)
    (hw : B.sharp w = (Scheme.ΓSpecIso (CommRingCat.of B.U)).hom.hom (D.u a b h).val)
    (h' : (gU B ≫ a) ≫ D.f = (gU B ≫ b) ≫ D.f) :
    tu B w = (D.u (gU B ≫ a) (gU B ≫ b) h').val := by
  rw [D.nat (gU B) a b h, tu_apply, hw, ← toΓ_nat, toΓ_hom]
  rfl

theorem exists_root (A : PAlg l) (n : ℕ) (w : (A.A)ˣ) : ∃ ω : (A.A)ˣ, ω ^ l ^ n = w := by
  have hs : ∀ (n : ℕ) (x : A.A), ∃ y : A.A, y ^ l ^ n = x := by
    intro n
    induction n with
    | zero => exact fun x => ⟨x, by simp⟩
    | succ n ih =>
      intro x
      obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius (R := A.A) (p := l)).2 x
      obtain ⟨z, hz⟩ := ih y
      exact ⟨z, by rw [pow_succ, pow_mul, hz]; exact hy⟩
  obtain ⟨y, hy⟩ := hs n w
  have hu : IsUnit y := (isUnit_pow_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)).1 (hy ▸ w.isUnit)
  obtain ⟨ω, rfl⟩ := hu
  exact ⟨ω, Units.ext (by simpa using hy)⟩

section Main
variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : Model l K} {C : Type 1} [Category.{0} C]

abbrev Ao (G : C ⥤ El M.P) (c : C) : PAlg l := (G.obj c).1.obj

abbrev mp (G : C ⥤ El M.P) {c c' : C} (φ : c ⟶ c') : Ao G c ⟶ Ao G c' := (G.map φ).1.hom

abbrev sg (G : C ⥤ El M.P) {c c' : C} (φ : c ⟶ c') : SU (Ao G c') ⟶ SU (Ao G c) :=
  Spec.map (CommRingCat.ofHom (PAlg.mapUg (mp G φ)))

abbrev sgU (G : C ⥤ El M.P) {c c' : C} (φ : c ⟶ c') :
    Spec (CommRingCat.of (Ao G c').U) ⟶ Spec (CommRingCat.of (Ao G c).U) :=
  Spec.map (CommRingCat.ofHom (PAlg.mapU (mp G φ)))

theorem sg_gU (G : C ⥤ El M.P) {c c' : C} (φ : c ⟶ c') : sg G φ ≫ gU (Ao G c) = gU (Ao G c') ≫ sgU G φ := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun x => PAlg.mapUg_algebraMap _ x

theorem sg_comp (G : C ⥤ El M.P) {c c' c'' : C} (φ : c ⟶ c') (ψ : c' ⟶ c'') :
    sg G (φ ≫ ψ) = sg G ψ ≫ sg G φ := by
  have e : mp G (φ ≫ ψ) = mp G φ ≫ mp G ψ := congrArg (fun t => t.1.hom) (G.map_comp φ ψ)
  rw [sg, e]
  exact (congrArg Spec.map ((UgR l).map_comp _ _)).trans (Spec.map_comp _ _)

theorem sgU_pt (G : C ⥤ El M.P) {c c' : C} (φ : c ⟶ c') : sgU G φ ≫ (G.obj c).2.1 = (G.obj c').2.1 :=
  congrArg Subtype.val (G.map φ).2

variable {D : LineData M.X} {D' : LineData (gb M)} {π : D'.Y ⟶ D.Y} {G : C ⥤ El M.P}

theorem hr_eq (hBC : D.IsBC (pullback.fst _ _ ≫ pullback.fst _ _ : gb M ⟶ M.X) D' π) (Λ : Lift G D)
    (p' : ∀ c, SU (Ao G c) ⟶ D'.Y) (hπ : ∀ c, p' c ≫ π = gU (Ao G c) ≫ Λ.p c) {c c' : C} (φ : c ⟶ c')
    (h : (sg G φ ≫ p' c) ≫ D'.f = p' c' ≫ D'.f) :
    tu (Ao G c') (Λ.w φ).val = (D'.u (sg G φ ≫ p' c) (p' c') h).val := by
  have h0 : (sgU G φ ≫ Λ.p c) ≫ D.f = Λ.p c' ≫ D.f := by
    rw [Category.assoc, Λ.hp, Λ.hp, sgU_pt]
  have h1 : (gU (Ao G c') ≫ sgU G φ ≫ Λ.p c) ≫ D.f = (gU (Ao G c') ≫ Λ.p c') ≫ D.f := by
    rw [Category.assoc, Category.assoc, ← Category.assoc (sgU G φ), h0, Category.assoc]
  have h2 : ((sg G φ ≫ p' c) ≫ π) ≫ D.f = (p' c' ≫ π) ≫ D.f := by
    have key : ∀ {V : Scheme.{0}} (t : V ⟶ D'.Y), (t ≫ π) ≫ D.f =
        (t ≫ D'.f) ≫ (pullback.fst _ _ ≫ pullback.fst _ _ : gb M ⟶ M.X) := fun t => by
      rw [Category.assoc, hBC.1, Category.assoc]
    rw [key, key, h]
  rw [tu_of_sharp D _ _ _ h0 _ (Λ.hw φ h0) h1, hBC.2.2 _ _ _ h h2]
  refine congrArg Units.val (u_congr D ?_ (hπ c').symm _ _)
  rw [Category.assoc, hπ, ← Category.assoc, ← sg_gU, Category.assoc]

abbrev tuU (A : PAlg l) : (A.A)ˣ →* (Γ(SU A, ⊤))ˣ := Units.map (tu A)

abbrev chU {c₁ c₂ : C} (G : C ⥤ El M.P) (ψ : c₁ ⟶ c₂) (a : ((Ao G c₁).A)ˣ) (b c : ((Ao G c₂).A)ˣ) : ((Ao G c₂).A)ˣ :=
  Units.map (PAlg.Hom.f (mp G ψ)).toMonoidHom a * b * c⁻¹

theorem map_tuU {c₁ c₂ : C} (G : C ⥤ El M.P) (ψ : c₁ ⟶ c₂) (a : ((Ao G c₁).A)ˣ) :
    Units.map (sg G ψ).appTop.hom.toMonoidHom (tuU (Ao G c₁) a) =
      tuU (Ao G c₂) (Units.map (PAlg.Hom.f (mp G ψ)).toMonoidHom a) :=
  Units.ext (tu_nat (mp G ψ) a.val)

theorem chain_val {c₁ c₂ : C} (G : C ⥤ El M.P) (ψ : c₁ ⟶ c₂) (a : ((Ao G c₁).A)ˣ) (b c : ((Ao G c₂).A)ˣ) :
    Units.map (sg G ψ).appTop.hom.toMonoidHom (tuU (Ao G c₁) a) * tuU (Ao G c₂) b * (tuU (Ao G c₂) c)⁻¹ =
      tuU (Ao G c₂) (chU G ψ a b c) := by
  rw [map_tuU, chU, map_mul, map_mul, map_inv]

theorem chain_pow {c₀ c₁ c₂ : C} (p' : ∀ c, SU (Ao G c) ⟶ D'.Y) (φ : c₀ ⟶ c₁) (ψ : c₁ ⟶ c₂) (χ : c₀ ⟶ c₂)
    (hχ : φ ≫ ψ = χ) (q : ℕ) (a : (Γ(SU (Ao G c₁), ⊤))ˣ) (b c : (Γ(SU (Ao G c₂), ⊤))ˣ)
    (h₁ : (sg G φ ≫ p' c₀) ≫ D'.f = p' c₁ ≫ D'.f) (h₂ : (sg G ψ ≫ p' c₁) ≫ D'.f = p' c₂ ≫ D'.f)
    (h₃ : (sg G χ ≫ p' c₀) ≫ D'.f = p' c₂ ≫ D'.f)
    (ha : a ^ q = D'.u (sg G φ ≫ p' c₀) (p' c₁) h₁) (hb : b ^ q = D'.u (sg G ψ ≫ p' c₁) (p' c₂) h₂)
    (hc : c ^ q = D'.u (sg G χ ≫ p' c₀) (p' c₂) h₃) :
    (Units.map (sg G ψ).appTop.hom.toMonoidHom a * b * c⁻¹) ^ q = 1 := by
  have h₄ : (sg G ψ ≫ sg G φ ≫ p' c₀) ≫ D'.f = (sg G ψ ≫ p' c₁) ≫ D'.f := by
    rw [Category.assoc, h₁, Category.assoc]
  rw [mul_pow, mul_pow, inv_pow, ← map_pow, ha, hb, hc, ← D'.nat (sg G ψ) _ _ h₁, D'.coc _ _ _ h₄ h₂]
  rw [u_congr D' (a' := sg G χ ≫ p' c₀) (b' := p' c₂) _ rfl _ h₃, mul_inv_cancel]
  rw [← hχ, sg_comp, Category.assoc]

abbrev tuP (H : RIn l) (r : Roots l) (G : C ⥤ El M.P) (n : ℕ) (c : C) :
    ((Ao G c).A)ˣ →* (Γ((probe H r (G ⋙ CategoryOfElements.π _) n).U c, ⊤))ˣ := tuU (Ao G c)

theorem chain_valP (H : RIn l) (r : Roots l) (G : C ⥤ El M.P) (n : ℕ) {c₁ c₂ : C} (ψ : c₁ ⟶ c₂)
    (a : ((Ao G c₁).A)ˣ) (b c : ((Ao G c₂).A)ˣ) :
    Units.map ((probe H r (G ⋙ CategoryOfElements.π _) n).S.map ψ).unop.appTop.hom.toMonoidHom (tuP H r G n c₁ a) *
      tuP H r G n c₂ b * (tuP H r G n c₂ c)⁻¹ = tuP H r G n c₂ (chU G ψ a b c) :=
  chain_val G ψ a b c

theorem pow_field (H : RIn l) (r : Roots l) (G : C ⥤ El M.P) (n : ℕ) (c : C)
    (f : LocallyConstant (SU (Ao G c)) (ZMod (l ^ n))) (u : ((Ao G c).A)ˣ)
    (h : IsPow (r.zeta (Ao G c) n) f (tu (Ao G c) u.val)) :
    IsPow ((probe H r (G ⋙ CategoryOfElements.π _) n).ζ c) f (tuP H r G n c u).val := h

theorem kum_of (H : RIn l) (r : Roots l) (G : C ⥤ El M.P) (n : ℕ)
    (z : Cn (probe H r (G ⋙ CategoryOfElements.π _) n).L 2) (p' : ∀ c, SU (Ao G c) ⟶ D'.Y)
    (hf : ∀ c, p' c ≫ D'.f = geomPt M (Ao G c) (G.obj c).2) (ω : ∀ (c c' : C), (c ⟶ c') → ((Ao G c').A)ˣ)
    (hfh : ∀ {c c' : C} (φ : c ⟶ c'), (sg G φ ≫ p' c) ≫ D'.f = p' c' ≫ D'.f)
    (hr : ∀ {c c' : C} (φ : c ⟶ c'), tuU (Ao G c') (ω c c' φ) ^ l ^ n = D'.u (sg G φ ≫ p' c) (p' c') (hfh φ))
    (hz : ∀ s : ComposableArrows C 2, IsPow ((probe H r (G ⋙ CategoryOfElements.π _) n).ζ (s.obj (Fin.last 2))) (z s)
      (tuP H r G n (s.obj (Fin.last 2)) (chU G (s.map' 1 2) (ω _ _ (s.map' 0 1)) (ω _ _ (s.map' 1 2)) (ω _ _ (s.map' 0 2)))).val) :
    Nonempty (IsKumCoc (pts H r M G n) D' z) :=
  ⟨{ p := p'
     hp := hf
     r := fun {c c'} φ => tuP H r G n c' (ω c c' φ)
     hr := fun φ => hr φ
     hz := fun s => by
       rw [chain_valP]
       exact hz s }⟩

theorem log_of (hN : LcNat) (H : RIn l) (r : Roots l) {D : LineData M.X} (G : C ⥤ El M.P) (n : ℕ) (Λ : Lift G D)
    (z : Cn (probe H r (G ⋙ CategoryOfElements.π _) n).L 2)
    (h : ∀ s : ComposableArrows C 2, IsLog (Ao G (s.obj (Fin.last 2))) n (tei (Ao G (s.obj (Fin.last 2))) (Λ.r s))
      ((ACris.periodT (untilt_epsilon (p := l)) : Acris l) • lcA (Ao G (s.obj (Fin.last 2))) n (z s))) :
    Λ.IsCoc n (tCo G n 2 (lcCo hN H r G n 2 z)) := h

theorem r_eq {D : LineData M.X} (Λ : Lift G D) (n : ℕ) (ω : ∀ (c c' : C), (c ⟶ c') → ((Ao G c').A)ˣ)
    (hω : ∀ (c c' : C) (φ : c ⟶ c'), ω c c' φ ^ l ^ n = Λ.w φ) (s : ComposableArrows C 2) :
    Λ.r s = (chU G (s.map' 1 2) (ω _ _ (s.map' 0 1)) (ω _ _ (s.map' 1 2)) (ω _ _ (s.map' 0 2))) ^ l ^ n := by
  rw [chU, mul_pow, mul_pow, inv_pow, ← map_pow, hω, hω, hω]
  rfl

end Main

theorem fKum (hR : RootPow) (hL : LcLog) : FKum := by
  intro hN l _ H r K M D D' π hBC C _ G Λ n
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hb : ∀ c, ∃ b : SU (Ao G c) ⟶ D'.Y, b ≫ π = gU (Ao G c) ≫ Λ.p c ∧
      b ≫ D'.f = geomPt M (Ao G c) (G.obj c).2 := fun c =>
    hBC.2.1 _ _ _ (by rw [Category.assoc, Λ.hp, geomPt_fst])
  choose p' hπ hf using hb
  have hω : ∀ (c c' : C) (φ : c ⟶ c'), ∃ ω : ((Ao G c').A)ˣ, ω ^ l ^ n = Λ.w φ := fun c c' φ => exists_root _ n _
  choose ω hω using hω
  have hfh : ∀ {c c' : C} (φ : c ⟶ c'), (sg G φ ≫ p' c) ≫ D'.f = p' c' ≫ D'.f := by
    intro c c' φ
    rw [Category.assoc, hf, hf]
    exact (pts H r M G n).nat φ
  have hr : ∀ {c c' : C} (φ : c ⟶ c'), tuU (Ao G c') (ω c c' φ) ^ l ^ n = D'.u (sg G φ ≫ p' c) (p' c') (hfh φ) := by
    intro c c' φ
    rw [← map_pow, hω c c' φ]
    exact Units.ext (hr_eq hBC Λ p' hπ φ _)
  have hz : ∀ s : ComposableArrows C 2, ∃ f : LocallyConstant (SU (Ao G (s.obj (Fin.last 2)))) (ZMod (l ^ n)),
      IsPow (r.zeta (Ao G (s.obj (Fin.last 2))) n) f
        (tu (Ao G (s.obj (Fin.last 2))) (chU G (s.map' 1 2) (ω _ _ (s.map' 0 1)) (ω _ _ (s.map' 1 2)) (ω _ _ (s.map' 0 2))).val) := by
    intro s
    refine (hR (l ^ n) _ _).1 _ ?_
    have h := chain_pow p' (s.map' 0 1) (s.map' 1 2) (s.map' 0 2) (by rw [← s.map_comp]; rfl) (l ^ n)
      (tuU _ (ω _ _ (s.map' 0 1))) (tuU _ (ω _ _ (s.map' 1 2))) (tuU _ (ω _ _ (s.map' 0 2)))
      (hfh _) (hfh _) (hfh _) (hr _) (hr _) (hr _)
    rw [chain_val] at h
    exact congrArg Units.val h
  choose z hz using hz
  refine ⟨z, kum_of H r G n z p' hf ω hfh hr fun s => pow_field H r G n _ _ _ (hz s), log_of hN H r G n Λ z fun s => ?_⟩
  have h := hL l H r (Ao G (s.obj (Fin.last 2))) (G.obj (s.obj (Fin.last 2))).1.property n _ (z s) (hz s)
  rw [← Units.val_pow_eq_pow_val, ← r_eq Λ n ω hω s] at h
  exact h

end GlobalTheory.CompanionTheory.FKum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionEqZeroIffCoeffsMem
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.ExpandKer

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem dxi_mul (i j : ℕ) :
    A.dxi 1 i * A.dxi 1 j = ((i + j).choose i : A.Acr 1) * A.dxi 1 (i + j) := by
  obtain ⟨-, hmul, -⟩ := _root_.GlobalTheory.CompanionTheory.FilMul.main A
  change A.mkAcr 1 (A.dxi0 i) * A.mkAcr 1 (A.dxi0 j)
    = ((i + j).choose i : A.Acr 1) * A.mkAcr 1 (A.dxi0 (i + j))
  rw [← map_mul, hmul, map_mul, map_natCast]

theorem aTo1_pi : A.aTo1 A.pi = -A.dxi 1 1 := by
  obtain ⟨-, -, hfac, -⟩ := _root_.GlobalTheory.CompanionTheory.FilMul.main A
  have h1 : A.dxi0 1 = algebraMap A.W A.Acr0 A.xi := by
    simpa using hfac 1
  have h2 : A.dxi 1 1 = A.toAcr 1 A.xi := by
    change A.mkAcr 1 (A.dxi0 1) = A.mkAcr 1 (algebraMap A.W A.Acr0 A.xi)
    rw [h1]
  rw [h2, ← A.aTo1_coeff, A.xi_coeff_zero, map_neg, neg_neg]

theorem toAcr_teichmuller (b : A.A) : A.toAcr 1 (WittVector.teichmuller l b) = A.aTo1 b := by
  rw [← A.aTo1_coeff, WittVector.teichmuller_coeff_zero]

theorem exists_coprime {m : ℕ} (hm : l ∣ m) {j : ℕ} (hj : j < l) :
    ∃ c : ℕ, c.Coprime l ∧ A.dxi 1 1 ^ j * A.dxi 1 m = (c : A.Acr 1) * A.dxi 1 (m + j) := by
  have hp : l.Prime := Fact.out
  induction j with
  | zero => exact ⟨1, Nat.coprime_one_left l, by simp⟩
  | succ j ih =>
    obtain ⟨c, hc, hcj⟩ := ih (Nat.lt_of_succ_lt hj)
    have hnd : ¬ l ∣ m + j + 1 := by
      intro h
      have h2 : l ∣ j + 1 := by
        rw [Nat.add_assoc] at h
        exact (Nat.dvd_add_right hm).mp h
      have := Nat.le_of_dvd (Nat.succ_pos j) h2
      omega
    refine ⟨c * (m + j + 1), Nat.Coprime.mul_left hc ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm, ?_⟩
    rw [pow_succ', mul_assoc, hcj, mul_left_comm, dxi_mul A 1 (m + j), Nat.choose_one_right]
    have e : 1 + (m + j) = m + (j + 1) := by omega
    rw [e]
    push_cast
    ring

theorem mem_of_coprime_mul {I : Ideal (A.Acr 1)} {c : ℕ} (hc : c.Coprime l) {x : A.Acr 1}
    (h : (c : A.Acr 1) * x ∈ I) : x ∈ I := by
  have hl : ((l : ℕ) : A.Acr 1) = 0 := by
    have e : ((l : ℕ) : A.Acr 1) = A.toAcr 1 (l : A.W) := by rw [map_natCast]
    rw [e]
    change Ideal.Quotient.mk _ (algebraMap A.W A.Acr0 (l : A.W)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.subset_span (by simp)
  have h1 : (1 : A.Acr 1) = (c : A.Acr 1) * (Nat.gcdA c l : A.Acr 1)
      + (l : A.Acr 1) * (Nat.gcdB c l : A.Acr 1) := by
    have h' := Nat.gcd_eq_gcd_ab c l
    rw [Nat.Coprime.gcd_eq_one hc, Nat.cast_one] at h'
    have h'' := congrArg (fun z : ℤ => (z : A.Acr 1)) h'
    push_cast at h''
    exact h''
  have hx : x = (Nat.gcdA c l : A.Acr 1) * ((c : A.Acr 1) * x) := by
    calc x = (1 : A.Acr 1) * x := (one_mul x).symm
      _ = _ := by rw [h1, hl]; ring
  rw [hx]
  exact I.mul_mem_left _ h

theorem inner_step (k : ℕ) {j : ℕ} (hj : j < l) (b : A.A)
    (h : A.aTo1 (A.pi ^ j * b) * A.dxi 1 (l * k) ∈ A.Fil 1 (l * k + j + 1)) :
    b ∈ Ideal.span {A.pi} := by
  obtain ⟨c, hc, hcj⟩ := exists_coprime A (dvd_mul_right l k) hj
  have hx : A.aTo1 b * A.dxi 1 (l * k + j) ∈ A.Fil 1 (l * k + j + 1) := by
    have e : A.aTo1 (A.pi ^ j * b) * A.dxi 1 (l * k)
        = (c : A.Acr 1) * ((-1) ^ j * (A.aTo1 b * A.dxi 1 (l * k + j))) := by
      rw [map_mul, map_pow, aTo1_pi A]
      calc (-A.dxi 1 1) ^ j * A.aTo1 b * A.dxi 1 (l * k)
          = (-1) ^ j * A.aTo1 b * (A.dxi 1 1 ^ j * A.dxi 1 (l * k)) := by ring
        _ = _ := by rw [hcj]; ring
    rw [e] at h
    have h2 := mem_of_coprime_mul A hc h
    have h3 : (-1 : A.Acr 1) ^ j * ((-1) ^ j * (A.aTo1 b * A.dxi 1 (l * k + j)))
        ∈ A.Fil 1 (l * k + j + 1) := Ideal.mul_mem_left _ _ h2
    have h4 : (-1 : A.Acr 1) ^ j * ((-1) ^ j * (A.aTo1 b * A.dxi 1 (l * k + j)))
        = A.aTo1 b * A.dxi 1 (l * k + j) := by
      rw [← mul_assoc, ← mul_pow]
      simp
    rwa [h4] at h3
  rw [← toAcr_teichmuller A b] at hx
  have hth := ((_root_.GlobalTheory.CompanionTheory.PerfFil.graded_mod_pow A 1 (l * k + j)).2 (WittVector.teichmuller l b)).mp hx
  have hz : A.aToU1 b = 0 := by
    have e := A.sharpMap_coeff (WittVector.teichmuller l b)
    rw [WittVector.teichmuller_coeff_zero] at e
    rw [e, Ideal.Quotient.eq_zero_iff_mem]
    exact hth
  obtain ⟨-, hker⟩ := GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker A
  rw [← hker]
  exact RingHom.mem_ker.mpr hz

theorem term_eq_zero {a : A.A} (h : a ∈ Ideal.span {A.pi ^ l}) (m : ℕ) :
    A.aTo1 a * A.dxi 1 m = 0 := by
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp h
  obtain ⟨-, -, -, h4⟩ := _root_.GlobalTheory.CompanionTheory.PerfFil.Expand.main A
  rw [map_mul, mul_assoc, h4, mul_zero]

theorem term_mem (c : ℕ →₀ A.A) (h0 : A.expand c = 0) (k : ℕ)
    (hk : ∀ i < k, c i ∈ Ideal.span {A.pi ^ l}) :
    A.aTo1 (c k) * A.dxi 1 (l * k) ∈ A.Fil 1 (l * k + l) := by
  obtain ⟨-, hadd, -, -⟩ := _root_.GlobalTheory.CompanionTheory.PerfFil.Expand.main A
  obtain ⟨-, -, -, -, hmap, -⟩ := _root_.GlobalTheory.CompanionTheory.FilMul.main A
  have hdx : ∀ m, A.dxi 1 m ∈ A.Fil 1 m := fun m => by
    rw [hmap]
    change A.mkAcr 1 (A.dxi0 m) ∈ _
    apply Ideal.mem_map_of_mem
    unfold CrystallineSemistableComparison.PAlg.Fil0
    exact Ideal.subset_span ⟨m, le_rfl, rfl⟩
  have hanti : ∀ r s : ℕ, r ≤ s → A.Fil 1 s ≤ A.Fil 1 r := by
    intro r s hrs
    rw [hmap, hmap]
    apply Ideal.map_mono
    unfold CrystallineSemistableComparison.PAlg.Fil0
    apply Ideal.span_mono
    rintro z ⟨i, hi, rfl⟩
    exact ⟨i, le_trans hrs hi, rfl⟩
  have hsingle : A.expand (Finsupp.single k (c k)) = A.aTo1 (c k) * A.dxi 1 (l * k) := by
    unfold CrystallineSemistableComparison.PAlg.expand
    rw [Finsupp.sum_single_index]
    simp
  have herase : A.expand (c.erase k) ∈ A.Fil 1 (l * k + l) := by
    unfold CrystallineSemistableComparison.PAlg.expand
    rw [Finsupp.sum]
    apply Ideal.sum_mem
    intro i hi
    have hik : i ≠ k := by
      rintro rfl
      simp at hi
    rw [Finsupp.erase_ne hik]
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · rw [term_eq_zero A (hk i hlt)]
      exact Ideal.zero_mem _
    · apply Ideal.mul_mem_left
      refine hanti _ _ ?_ (hdx (l * i))
      calc l * k + l = l * (k + 1) := by ring
        _ ≤ l * i := Nat.mul_le_mul (le_refl l) hgt
  have hsplit := hadd (Finsupp.single k (c k)) (c.erase k)
  rw [Finsupp.single_add_erase, h0, hsingle] at hsplit
  have e : A.aTo1 (c k) * A.dxi 1 (l * k) = -A.expand (c.erase k) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hsplit.symm
  rw [e]
  exact (Ideal.neg_mem_iff _).mpr herase

theorem fil_anti {r s : ℕ} (h : r ≤ s) : A.Fil 1 s ≤ A.Fil 1 r := by
  obtain ⟨-, -, -, -, hmap, -⟩ := _root_.GlobalTheory.CompanionTheory.FilMul.main A
  rw [hmap, hmap]
  apply Ideal.map_mono
  unfold CrystallineSemistableComparison.PAlg.Fil0
  apply Ideal.span_mono
  rintro z ⟨i, hi, rfl⟩
  exact ⟨i, le_trans h hi, rfl⟩

theorem coeff_mem (c : ℕ →₀ A.A) (h0 : A.expand c = 0) (k : ℕ)
    (hk : ∀ i < k, c i ∈ Ideal.span {A.pi ^ l}) : c k ∈ Ideal.span {A.pi ^ l} := by
  have hT := term_mem A c h0 k hk
  have key : ∀ j, j ≤ l → c k ∈ Ideal.span {A.pi ^ j} := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (ih (Nat.le_of_succ_le hj))
      have h1 : A.aTo1 (A.pi ^ j * b) * A.dxi 1 (l * k) ∈ A.Fil 1 (l * k + j + 1) := by
        rw [mul_comm (A.pi ^ j) b, hb]
        exact fil_anti A (by omega) hT
      obtain ⟨b', hb'⟩ := Ideal.mem_span_singleton'.mp (inner_step A k (Nat.lt_of_succ_le hj) b h1)
      rw [← hb, ← hb', pow_succ]
      exact Ideal.mem_span_singleton'.mpr ⟨b', by ring⟩
  exact key l le_rfl

theorem expand_eq_zero_iff : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (c : ℕ →₀ A.A),
    A.expand c = 0 ↔ ∀ k, c k ∈ Ideal.span {A.pi ^ l} := by
  intro l _ A c
  constructor
  · intro h0 k
    refine Nat.strong_induction_on k ?_
    intro k ih
    exact coeff_mem A c h0 k ih
  · intro h
    unfold CrystallineSemistableComparison.PAlg.expand
    rw [Finsupp.sum]
    apply Finset.sum_eq_zero
    intro i _
    exact term_eq_zero A (h i) _

end GlobalTheory.CompanionTheory.ExpandKer
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LcMorCup
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtCupF

variable {l : ℕ} [Fact l.Prime]

noncomputable def lcRing (hS : LcSpec) (H : RIn l) (A : PAlg l) (hA : A.IsTest) (n : ℕ) :
    LocallyConstant (SU A) (ZMod (l ^ n)) →+* A.Acr n where
  toFun := lcA A n
  map_one' := (hS l H A hA n).2.1
  map_mul' := (hS l H A hA n).2.2.1
  map_zero' := map_zero _
  map_add' := map_add _

theorem lcMor_cup (hM : MorCup) (hS : LcSpec) (hN : LcNat) (H : RIn l) (r : Roots l) {C : Type 1} [Category.{0} C]
    (T : C ⥤ Test l) (n p q m : ℕ) (h : p + q = m) (x : CH.H (probe H r T n).L p) (y : CH.H (probe H r T n).L q) :
    (lcMor hN H r T n).pull m ((mulP (lcF (probe H r T n).S (l ^ n))).cup h x y) =
      (mulP ((T ⋙ testι l) ⋙ AcrA l n)).cup h ((lcMor hN H r T n).pull p x) ((lcMor hN H r T n).pull q y) :=
  (hM ℤ (Acris l) (Int.castRingHom (Acris l)) C (lcF (probe H r T n).S (l ^ n)) ((T ⋙ testι l) ⋙ AcrA l n)
    (lcMor hN H r T n) (fun c => lcRing hS H (T.obj c).obj (T.obj c).property n) (fun c x => rfl)).2 p q m h x y

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem eG_cup (hE : EtCup) (hM : MorCup) (hS : LcSpec) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l)
    (M : Model l K) {C : Type 1} [Category.{0} C] (G : C ⥤ El M.P) (n : ℕ) (i i' i'' : ℤ) (hi : i + i' = i'')
    (j j' j'' : ℕ) (hj : j + j' = j'') (x : Ht (l ^ n) (sch.obj (gb M)) j i) (y : Ht (l ^ n) (sch.obj (gb M)) j' i') :
    eG hN H r M G n i'' j'' ((cup (l ^ n) x y).cast (by omega) hi) =
      (mulP ((((G ⋙ CategoryOfElements.π _) ⋙ testι l)) ⋙ AcrA l n)).cup hj (eG hN H r M G n i j x) (eG hN H r M G n i' j' y) := by
  have h1 := hE E.gen E.tw (l ^ n) C (probe H r (G ⋙ CategoryOfElements.π _) n) (gb M)
    (pts H r M G n) i i' i'' hi j j' j'' hj x y
  have h2 := lcMor_cup hM hS hN H r (G ⋙ CategoryOfElements.π _) n j j' j'' hj
    ((pts H r M G n).et i j x) ((pts H r M G n).et i' j' y)
  exact (congrArg ((lcMor hN H r (G ⋙ CategoryOfElements.π _) n).pull j'') h1).trans h2

theorem fCup : CrystallineSemistableComparison.E.EtCup → CrystallineSemistableComparison.E.MorCup → CrystallineSemistableComparison.E.LcSpec → CrystallineSemistableComparison.E.FCup := by
  intro hE hM hS E hN l _ H r K M n i i' i'' hi j j' j'' hj x y
  exact eG_cup hE hM hS E hN H r M (𝟭 _) n i i' i'' hi j j' j'' hj x y

end GlobalTheory.CompanionTheory.EtCupF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalExpProductDecompositionStatement
section
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_exp_product_decomposition : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → ∀ 𝔤 𝔨 𝔟 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) → (∃ V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤) → 𝔨 ≤ 𝔤 → 𝔟 ≤ 𝔤 → 𝔤 ≤ 𝔨 ⊔ 𝔟 → ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G → ∃ X ∈ 𝔨, ∃ Y ∈ 𝔟, g = NormedSpace.exp X * NormedSpace.exp Y := by
  first | exact @GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_mul_exp_of_isLinRed | exact GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_mul_exp_of_isLinRed | (intros; apply GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_mul_exp_of_isLinRed <;> assumption)
end

