module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0037
public import Development.EtaleCohomology.EtaleSheaves.Bundle0035
public import Development.EtaleCohomology.EtaleSheaves.Bundle0041
public import Development.EtaleCohomology.EtaleSheaves.Bundle0007

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.EmptyH2
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf

namespace LateralTheory.E.EmptyH₂

theorem sec_subsingleton {R : Type} [CommRing R] (F : Shv R) (Y : Scheme.{0}) [IsEmpty Y] :
    Subsingleton (Sec F Y) := by
  have hT := Sheaf.isTerminalOfBotCover F Y (Scheme.bot_mem_grothendieckTopology (P := @Etale) Y)
  exact (ModuleCat.isZero_iff_subsingleton).1 hT.isZero

theorem h_empty (hH : Hyp) {R : Type} [CommRing R] (F : Shv R) (Y : Scheme.{0}) [IsEmpty Y] (n : ℤ)
    (x : H R (sch.obj Y) F n) : x = 0 := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have := (hH.a9 R F).1 (sch.obj Y) n hn
    exact Subsingleton.elim _ _
  · obtain ⟨e, -, -⟩ := (hH.a9 R F).2
    have := sec_subsingleton F Y
    rw [← (e Y).apply_symm_apply x, Subsingleton.elim ((e Y).symm x) 0, map_zero]
  · obtain ⟨Z, f, -, -, hf⟩ := hH.a5 R Y F n hn x
    have : IsIso (sch.map f) := inferInstance
    have h1 : pull R (inv (sch.map f) ≫ sch.map f) F n x = 0 := by rw [pull_comp, hf, map_zero]
    simpa [pull_id] using h1

theorem EmptyH_of : LateralTheory.E.InjStepPf.EmptyH := by
  intro hH q X S p U hU i n x
  have : IsEmpty U := ⟨fun u => by
    have h : (u.1 : S) ∈ (U : Set S) := u.2
    rw [hU] at h; exact h⟩
  have : IsEmpty (overO p U) := ⟨fun z => isEmptyElim ((pullback.snd p U.ι).base z)⟩
  exact h_empty hH _ _ n x

end LateralTheory.E.EmptyH₂
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleEmbedding
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.EmbedPf

def AffClosed : Prop := ∀ (A : Type) [CommRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A))
  [LocallyOfFiniteType p] (V : X.Opens), IsAffineOpen V →
    ∃ (n : ℕ) (e : V.toScheme ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) A))), IsClosedImmersion e ∧
      e ≫ Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A))) = V.ι ≫ p

def Chart : Prop := ∀ (A : Type) [CommRing A] (n : ℕ), ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of A))
  (j : Spec (CommRingCat.of (MvPolynomial (Fin n) A)) ⟶ P), IterLine q ∧ IsOpenImmersion j ∧
    j ≫ q = Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)))

theorem affClosed : AffClosed := by
  intro A _ X p _ V hV
  haveI : IsAffine V.toScheme := hV
  have hfT : LocallyOfFiniteType (V.ι ≫ p) := inferInstance
  have happ := HasRingHomProperty.appTop @LocallyOfFiniteType (V.ι ≫ p) hfT
  let g : CommRingCat.of A ⟶ Γ(V.toScheme, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (V.ι ≫ p).appTop
  have hg : g.hom.FiniteType := by
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    exact RingHom.FiniteType.comp happ h1
  letI : Algebra A Γ(V.toScheme, ⊤) := g.hom.toAlgebra
  have hft : Algebra.FiniteType A Γ(V.toScheme, ⊤) := hg
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
  refine ⟨n, V.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom), ?_, ?_⟩
  · have hs := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ.toRingHom) hφ
    have hi : IsClosedImmersion V.toScheme.toSpecΓ := inferInstance
    exact @IsClosedImmersion.comp _ _ _ _ _ hi hs
  · have hcomp : CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)) ≫ CommRingCat.ofHom φ.toRingHom = g := by
      ext a
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
      exact φ.commutes a
    have h2 : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A))) =
        Spec.map g := by rw [← Spec.map_comp, hcomp]
    have h3 : V.toScheme.toSpecΓ ≫ Spec.map g = V.ι ≫ p := by
      have hn := Scheme.toSpecΓ_naturality (V.ι ≫ p)
      have h4 : Spec.map g = Spec.map (V.ι ≫ p).appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv :=
        Spec.map_comp _ _
      rw [h4, ← Category.assoc, ← hn, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    refine Eq.trans ?_ h3
    rw [Category.assoc]
    exact congrArg (fun t => V.toScheme.toSpecΓ ≫ t) h2

theorem Embed_of (hA : AffClosed) (hC : Chart) : LateralTheory.E.ChowGraphCut.Embed := by
  intro A _ X p _ V hV
  obtain ⟨n, e, he, hep⟩ := hA A p V hV
  obtain ⟨P, q, j, hq, hj, hjq⟩ := hC A n
  haveI := hj
  haveI := he
  refine ⟨P, q, j.opensRange, e ≫ j.isoOpensRange.hom, hq, inferInstance, ?_⟩
  rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, hjq, hep]

end LateralTheory.E.EmbedPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FibreEqvPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.FibPf LateralTheory.E.FibClosedPf LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibreEqvPf

theorem eqv_snd_snd {q : ℕ} {i : ℤ} {Z S K L : Scheme.{0}} (c : Z ⟶ S) (t : L ⟶ S) (k : K ⟶ L) :
    Eqv _ (sch.map (pullback.snd (pullback.snd c t) k)) (tw q i) ↔ Eqv _ (sch.map (pullback.snd c (k ≫ t))) (tw q i) := by
  have e := pullbackLeftPullbackSndIso_hom_snd c t k
  rw [← e, Functor.map_comp]
  exact ⟨fun h => eqv_right h (eqv_iso (pullbackLeftPullbackSndIso c t k) q i), fun h => eqv_comp (eqv_iso _ q i) h⟩

theorem eqv_snd_iso {q : ℕ} {i : ℤ} {Z S K K' : Scheme.{0}} (c : Z ⟶ S) (T : K ⟶ S) (ρ : K' ⟶ K) [IsIso ρ]
    (h : Eqv _ (sch.map (pullback.snd c T)) (tw q i)) : Eqv _ (sch.map (pullback.snd c (ρ ≫ T))) (tw q i) := by
  rw [← eqv_snd_snd]
  have w : sch.map (pullback.snd (pullback.snd c T) ρ) ≫ sch.map ρ = sch.map (pullback.fst (pullback.snd c T) ρ) ≫ sch.map (pullback.snd c T) := by
    rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]
  refine eqv_left (g := sch.map ρ) ?_ (eqv_iso (asIso ρ) q i)
  rw [w]
  exact eqv_comp (eqv_iso (asIso (pullback.fst (pullback.snd c T) ρ)) q i) h

def StalkFib : Prop := Hyp → HZero → AICAcyc → ∀ (q : ℕ) (i : ℤ) {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c]
  [QuasiSeparated c] [IsDominant c], AICSch Z → AICSch S → ∀ x : S, IsUnit (q : S.presheaf.stalk x) →
  Eqv _ (sch.map (pullback.snd c (S.fromSpecStalk x))) (tw q i)

theorem residue_bij {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (f : R →+* R') [IsLocalHom f]
    (hf : Function.Surjective f) : Function.Bijective (IsLocalRing.ResidueField.map f) := by
  refine ⟨(IsLocalRing.ResidueField.map f).injective, fun y => ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨IsLocalRing.residue R x, IsLocalRing.ResidueField.map_residue f x⟩

theorem geom (H : Hyp) (h0 : HZero) (hA : AICAcyc) (hS : StalkSHS) (hF : StalkFib) (q : ℕ) (i : ℤ) {Z S : Scheme.{0}}
    (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c] (hZs : AICSch Z) (hSs : AICSch S)
    (hB : ∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t))
    (x : S) (hu : IsUnit (q : S.presheaf.stalk x)) :
    Eqv _ (sch.map (pullback.snd c (cpt (S.presheaf.stalk x) ≫ S.fromSpecStalk x))) (tw q i) := by
  have hsh := hS S hSs x
  obtain ⟨_, _⟩ := id hsh
  have hx := hF H h0 hA q i c hZs hSs x hu
  have hpb : Eqv _ (sch.map (pullback.fst (pullback.snd c (S.fromSpecStalk x)) (cpt (S.presheaf.stalk x)))) (tw q i) :=
    hB _ hsh hu (S.fromSpecStalk x)
  have hE1 : Eqv _ (sch.map (cpt (S.presheaf.stalk x))) (tw q i) := H.e1 q _ (IsLocalRing.maximalIdeal _) hu i
  rw [← eqv_snd_snd]
  refine eqv_left (g := sch.map (cpt (S.presheaf.stalk x))) ?_ hE1
  rw [← Functor.map_comp, ← pullback.condition, Functor.map_comp]
  exact eqv_comp hpb hx

theorem FibreEqv_of (hS : StalkSHS) (hF : StalkFib) : FibreEqv := by
  intro H h0 hA q i A _ _ hq Z S c p _ _ _ _ _ hZs hSs hB s
  set j := pullback.fst p (cpt A)
  have h1 : SurjectiveOnStalks (cpt A) :=
    SurjectiveOnStalks.Spec_iff.2 (RingHom.surjectiveOnStalks_of_surjective IsLocalRing.residue_surjective)
  have h2 : SurjectiveOnStalks j := MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback p (cpt A)).flip h1
  have hsurj : Function.Surjective (j.stalkMap s).hom := j.stalkMap_surjective s
  have hu0 : IsUnit (q : Γ(S, ⊤)) := unit_of hq p
  have hu : IsUnit (q : S.presheaf.stalk (j s)) := by
    simpa using hu0.map (S.presheaf.germ ⊤ (j s) trivial).hom
  have hbij := residue_bij (j.stalkMap s).hom hsurj
  let ρ : Spec (CommRingCat.of (IsLocalRing.ResidueField ((pullback p (cpt A)).presheaf.stalk s))) ⟶
      Spec (CommRingCat.of (IsLocalRing.ResidueField (S.presheaf.stalk (j s)))) :=
    Spec.map (RingEquiv.ofBijective _ hbij).toCommRingCatIso.hom
  have sq : cpt ((pullback p (cpt A)).presheaf.stalk s) ≫ (pullback p (cpt A)).fromSpecStalk s ≫ j =
      ρ ≫ cpt (S.presheaf.stalk (j s)) ≫ S.fromSpecStalk (j s) := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk j, ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [ρ, cpt, ← Spec.map_comp]
    congr 1
  rw [eqv_snd_snd, sq]
  exact eqv_snd_iso c _ ρ (geom H h0 hA hS hF q i c hZs hSs hB (j s) hu)

end LateralTheory.E.FibreEqvPf

namespace LateralTheory.E.FibreEqvPf

def BaseAIC : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, AICSch (pullback c (S.fromSpecStalk x))

def StalkAIC : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, AICSch (Spec (S.presheaf.stalk x))

theorem StalkFib_of (hZB : BaseAIC) (hSA : StalkAIC) : StalkFib := by
  intro H h0 hA q i Z S c _ _ _ hZs hSs x hu
  have hB := hZB c hZs hSs x
  have hK := hSA S hSs x
  have : IsIntegral (pullback c (S.fromSpecStalk x) : Scheme.{0}) := hB.1
  have : ConnectedSpace (pullback c (S.fromSpecStalk x) : Scheme.{0}) := inferInstance
  have : CompactSpace (pullback c (S.fromSpecStalk x) : Scheme.{0}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd c (S.fromSpecStalk x))
  have : QuasiSeparatedSpace (pullback c (S.fromSpecStalk x) : Scheme.{0}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd c (S.fromSpecStalk x))
  have hu1 : IsUnit (q : Γ(Spec (S.presheaf.stalk x), ⊤)) := unit_of (A := S.presheaf.stalk x) hu (𝟙 _)
  have hu2 : IsUnit (q : Γ(pullback c (S.fromSpecStalk x), ⊤)) :=
    unit_of (A := S.presheaf.stalk x) hu (pullback.snd c (S.fromSpecStalk x))
  exact eqv_of H.a9 _ (h0 H q (pullback.snd c (S.fromSpecStalk x)) hK inferInstance hu1 i) (fun n hn => hA H q _ hB hu2 n i hn)
    (fun n hn => hA H q _ hK hu1 n i hn)

end LateralTheory.E.FibreEqvPf

namespace LateralTheory.E.FibreEqvPf

def StalkAICRing : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, AIC (S.presheaf.stalk x)

def SpecAIC : Prop := ∀ (B : CommRingCat.{0}), IsDomain B → AIC B → AICSch (Spec B)

theorem StalkAIC_of (h1 : StalkAICRing) (h2 : SpecAIC) : StalkAIC := by
  intro S hS x
  have : IsIntegral S := hS.1
  exact h2 _ inferInstance (h1 S hS x)

end LateralTheory.E.FibreEqvPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FibreIdem
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.StdChartsProof

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

def Restr (B : Subalgebra A K) (t : K) (Q : PrimeSpectrum (AdjoinInv B t)) (S : Subalgebra A K) (x : PrimeSpectrum S) :
    Prop := ∀ s : S, s ∈ x.asIdeal ↔ ∃ d ∈ Q.asIdeal, (d : K) = (s : K)

structure Cover {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K) : Prop where
  ex : ∃ (jU : Spec (CommRingCat.of B) ⟶ Z) (jV : Spec (CommRingCat.of C) ⟶ Z),
    IsOpenImmersion jU ∧ IsOpenImmersion jV ∧ Set.range jU.base ∪ Set.range jV.base = Set.univ ∧
    jU ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A B)) ∧ jV ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A C)) ∧
    ∀ (x : PrimeSpectrum B) (y : PrimeSpectrum C), jU.base x = jV.base y ↔
      ∃ Q : PrimeSpectrum (AdjoinInv B t), Restr B t Q B x ∧ Restr B t Q C y

def ChartsGeom : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z →
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧ Cover p B C t

def FibreIdem : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K] {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K), Charts B C t → Cover p B C t →
    ∀ W : Set ↑(pullback p (cpt A)), IsClopen W → ∃ e f : K, IdemPair B C t e f ∧
      ((e ∈ mS B ∧ f ∈ mS C) → W = ∅) ∧ ((e - 1 ∈ mS B ∧ f - 1 ∈ mS C) → W = Set.univ)

theorem StdCharts_of (hG : ChartsGeom) (hF : FibreIdem) : LateralTheory.E.StandardEtaleChartsIdempotentGluing.StdCharts := by
  intro A _ _ Z p hIL hZ
  obtain ⟨K, hK, hA, B, C, t, hc, hint, hcov⟩ := hG A p hIL hZ
  exact ⟨K, hK, hA, B, C, t, hc, hint, fun W hW => hF A K p B C t hc hcov W hW⟩

end LateralTheory.E.StdChartsProof
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FiltPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.TruncationPieces

namespace LateralTheory.E.FiltPf

namespace Tri

open Pretriangulated
universe u v

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (CategoryTheory.shiftFunctor D n)] [Pretriangulated D]

def RelY (Y : ℤ → D) (n : ℤ) {A B : D} (g : A ⟶ B) : Prop :=
  Function.Surjective (fun x : B ⟶ Y (n - 1) => g ≫ x) ∧ Function.Injective (fun x : B ⟶ Y n => g ≫ x)

omit [HasZeroObject D] [HasShift D ℤ] [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D] in
theorem inj_iff {A B X : D} (g : A ⟶ B) :
    Function.Injective (fun x : B ⟶ X => g ≫ x) ↔ ∀ x : B ⟶ X, g ≫ x = 0 → x = 0 := by
  constructor
  · intro h x hx; exact h (by simpa using hx)
  · intro h x y hxy
    have := h (x - y) (by simp only [Preadditive.comp_sub]; exact sub_eq_zero.2 hxy)
    exact sub_eq_zero.1 this

theorem relY_mid (T₁ T₂ : Triangle D) (h₁ : T₁ ∈ distTriang D) (h₂ : T₂ ∈ distTriang D) (φ : T₁ ⟶ T₂)
    (Y : ℤ → D) (e : ∀ n, Y n ≅ (Y (n - 1))⟦(1 : ℤ)⟧) (n : ℤ)
    (ha : RelY Y n φ.hom₁) (hc : RelY Y n φ.hom₃) : RelY Y n φ.hom₂ := by
  have hci := (inj_iff _).1 hc.2
  have hai := (inj_iff _).1 ha.2
  refine ⟨fun x => ?_, (inj_iff _).2 fun d hd => ?_⟩
  · obtain ⟨y, hy⟩ := ha.1 (T₁.mor₁ ≫ x)
    simp only at hy
    have ho : T₂.mor₃ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map y ≫ (e n).inv = 0 := by
      apply hci
      rw [← Category.assoc, ← φ.comm₃, Category.assoc, ← Functor.map_comp_assoc, hy, Functor.map_comp_assoc,
        ← Category.assoc, comp_distTriang_mor_zero₃₁ T₁ h₁, zero_comp]
    have ho' : T₂.rotate.mor₂ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map y = 0 := by
      have := congrArg (· ≫ (e n).hom) ho
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] at this
      exact this
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ h₂) _ ho'
    obtain ⟨(z : T₂.obj₂ ⟶ Y (n - 1)), rfl⟩ := (CategoryTheory.shiftFunctor D (1 : ℤ)).map_surjective g
    have hyz : y = T₂.mor₁ ≫ (-z) := by
      apply (CategoryTheory.shiftFunctor D (1 : ℤ)).map_injective
      rw [hg]
      simp only [Triangle.rotate_mor₃, Functor.map_comp, Functor.map_neg, Preadditive.comp_neg]
      exact Preadditive.neg_comp _ _
    have hw : T₁.mor₁ ≫ (x - φ.hom₂ ≫ (-z)) = 0 := by
      rw [Preadditive.comp_sub, ← hy, hyz, ← Category.assoc, ← φ.comm₁, Category.assoc, sub_self]
    obtain ⟨w, hw⟩ := Triangle.yoneda_exact₂ _ h₁ _ hw
    obtain ⟨w', hw'⟩ := hc.1 w
    simp only at hw'
    refine ⟨-z + T₂.mor₂ ≫ w', ?_⟩
    simp only
    rw [Preadditive.comp_add, ← Category.assoc, ← φ.comm₂, Category.assoc, hw', ← hw]
    abel
  · have h1 : T₂.mor₁ ≫ d = 0 := by
      apply hai
      rw [← Category.assoc, ← φ.comm₁, Category.assoc, hd, comp_zero]
    obtain ⟨h, rfl⟩ := Triangle.yoneda_exact₂ _ h₂ _ h1
    have h3 : T₁.mor₂ ≫ φ.hom₃ ≫ h = 0 := by
      rw [← Category.assoc, φ.comm₂, Category.assoc, hd]
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ _ h₁ _ h3
    obtain ⟨k', hk'⟩ := (CategoryTheory.shiftFunctor D (1 : ℤ)).map_surjective (k ≫ (e n).hom)
    obtain ⟨k'', hk''⟩ := ha.1 k'
    simp only at hk''
    have hm : h = T₂.mor₃ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map k'' ≫ (e n).inv := by
      rw [← sub_eq_zero]
      apply hci
      rw [Preadditive.comp_sub, hk, ← Category.assoc φ.hom₃, ← φ.comm₃, Category.assoc, ← Functor.map_comp_assoc,
        hk'', hk', Category.assoc, Iso.hom_inv_id, Category.comp_id, sub_self]
    rw [hm, ← Category.assoc, comp_distTriang_mor_zero₂₃ _ h₂, zero_comp]

end Tri

section Bridge
open CochainComplex CochainComplex.HomComplex
variable (R : Type) [CommRing R]

abbrev Yres (F : Shv R) (m : ℤ) : HomotopyCategory (Shv R) (ComplexShape.up ℤ) :=
  (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦m⟧)

theorem pull_eq_comp {K L : Cx R} (f : K ⟶ L) (F : Shv R) (m : ℤ) :
    (fun g : (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj L ⟶ Yres R F m =>
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map f ≫ g) =
      (CohomologyClass.homAddEquiv) ∘ (HK.pull R f F m) ∘ (CohomologyClass.homAddEquiv.symm) := by
  funext g
  simp only [Function.comp_apply, CohomologyClass.homAddEquiv_apply, LateralTheory.E.E8.ExciseCut.ConeZeroPf.pull_toHom]
  congr 1
  exact (CohomologyClass.homAddEquiv.apply_symm_apply g).symm

theorem relK_iff {K L : Cx R} (f : K ⟶ L) (F : Shv R) (n : ℤ) :
    RelK R F n f ↔ Tri.RelY (Yres R F) n ((HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map f) := by
  unfold Tri.RelY RelK
  rw [pull_eq_comp, pull_eq_comp, EquivLike.comp_surjective, EquivLike.surjective_comp,
    EquivLike.comp_injective, EquivLike.injective_comp]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1 (n - 1) (by omega), h2⟩
  · rintro ⟨h1, h2⟩; refine ⟨fun m hm => ?_, h2⟩; obtain rfl : m = n - 1 := (by omega)
    exact h1

def yresIso (F : Shv R) (m : ℤ) : Yres R F m ≅ (Yres R F (m - 1))⟦(1 : ℤ)⟧ :=
  LateralTheory.E.E8.ExciseCut.ConeZeroPf.shIso R (res R F) m

end Bridge

def pieceC (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (p : ℕ) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (K.X (-(p : ℤ))) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (L.X (-(p : ℤ))) :=
  (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (f.f (-(p : ℤ)))

def Tower : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K L : Cx R} (f : K ⟶ L) (n : ℤ),
  (∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)) →
  (∀ p : ℕ, RelK R F n (pieceC R f p)) → RelK R F n f

def TowerFin : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K L : Cx R} (f : K ⟶ L) (n : ℤ) (P : ℕ),
  (∀ i : ℤ, (0 < i ∨ i < -(P : ℤ)) → IsZero (K.X i) ∧ IsZero (L.X i)) →
  (∀ p : ℕ, RelK R F n (pieceC R f p)) → RelK R F n f

def Trunc : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K L : Cx R} (f : K ⟶ L) (n : ℤ),
  (∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)) →
  ∃ (P : ℕ) (K' L' : Cx R) (f' : K' ⟶ L'),
    (∀ i : ℤ, (0 < i ∨ i < -(P : ℤ)) → IsZero (K'.X i) ∧ IsZero (L'.X i)) ∧
    ((∀ p : ℕ, RelK R F n (pieceC R f p)) → ∀ p : ℕ, RelK R F n (pieceC R f' p)) ∧
    (RelK R F n f' → RelK R F n f)

theorem tower_of (hB : TowerFin) (hT : Trunc) : Tower := by
  intro R _ F K L f n hz hp
  obtain ⟨P, K', L', f', hz', hpp, hback⟩ := hT R F f n hz
  exact hback (hB R F f' n P hz' (hpp hp))

theorem chains_X_isZero (R : Type) [CommRing R] (U : Spc) (i : ℤ) (hi : 0 < i) : IsZero (((chains R).obj U).X i) := by
  change IsZero ((((chainsN R).obj U).extend ComplexShape.embeddingDownNat).X i)
  apply HomologicalComplex.isZero_extend_X
  intro j hj
  have e : ComplexShape.embeddingDownNat.f j = -(j : ℤ) := rfl
  omega

end LateralTheory.E.FiltPf

open LateralTheory.E.FiltPf in
theorem LateralTheory.E.TruncationPieces.Filt_of_tower (hT : Tower) : LateralTheory.E.TruncationPieces.Filt := by
  intro R _ F U E u n h
  exact hT R F ((chains R).map u) n (fun i hi => ⟨chains_X_isZero R U i hi, chains_X_isZero R E i hi⟩) h

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IterCompPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.IterCompPf

theorem isLine_iso_comp {L L' S : Scheme.{0}} (e : L' ⟶ L) [IsIso e] {l : L ⟶ S} (h : IsLine l) :
    IsLine (e ≫ l) :=
  h.bc (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback e (e ≫ l) l (𝟙 S))

theorem iterLine_iso_comp {T S Y : Scheme.{0}} {k : T ⟶ S} (hk : IterLine k) (e : Y ⟶ T) [IsIso e] :
    IterLine (e ≫ k) := by
  cases hk with
  | iso k' hk' => exact IterLine.iso _ inferInstance
  | comp l k' hl hk' =>
    rw [← Category.assoc]
    exact IterLine.comp _ _ (isLine_iso_comp e hl) hk'

theorem IterComp_of : LateralTheory.E.ChowGraphCut.IterComp := by
  intro P T S l k hl hk
  induction hl with
  | iso e he => exact iterLine_iso_comp hk e
  | comp l₁ k₁ hl₁ _ ih =>
    rw [Category.assoc]
    exact IterLine.comp _ _ hl₁ ih

end LateralTheory.E.IterCompPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LZIdemSumApprox
section
noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.IdempotentLiftingAlt

def LZIdemSumNoeth : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : Type) [Field K]
  [Algebra A K] (B C : Subalgebra A K) (t : K), Charts B C t → B.FG → C.FG → ∀ e f : K, IdemPair B C t e f →
  e - f ∈ mS B ⊔ mS C

def LZIdemSumApprox : Prop := LZIdemSumNoeth → ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K]
  [Algebra A K] (B C : Subalgebra A K) (t : K), Charts B C t → ∀ e f : K, IdemPair B C t e f →
  e - f ∈ mS B ⊔ mS C

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

theorem mS_le (S : Subalgebra A K) : mS S ≤ Subalgebra.toSubmodule S := by
  unfold mS
  exact Submodule.smul_le_right

theorem lift_of_sum (B C : Subalgebra A K) (e f : K) (he : e ∈ B) (hf : f ∈ C) (h : e - f ∈ mS B ⊔ mS C) :
    ∃ g ∈ B, g ∈ C ∧ g - e ∈ mS B ∧ g - f ∈ mS C := by
  obtain ⟨β, hβ, γ, hγ, hsum⟩ := Submodule.mem_sup.mp h
  have hβB : β ∈ B := mS_le B hβ
  have hγC : γ ∈ C := mS_le C hγ
  refine ⟨e - β, B.sub_mem he hβB, ?_, ?_, ?_⟩
  · have : e - β = f + γ := by linear_combination -hsum
    rw [this]; exact C.add_mem hf hγC
  · have : e - β - e = -β := by ring
    rw [this]; exact (mS B).neg_mem hβ
  · have : e - β - f = γ := by linear_combination -hsum
    rw [this]; exact hγ

theorem IdemLift_of (hN : LZIdemSumNoeth) (hA : LZIdemSumApprox) : LateralTheory.E.StandardEtaleChartsIdempotentGluing.IdemLift := by
  intro A _ _ _ K _ _ B C t hc e f hp
  exact lift_of_sum B C e f hp.1 hp.2.1 (hA hN A K B C t hc e f hp)

end LateralTheory.E.IdempotentLiftingAlt
end
end

